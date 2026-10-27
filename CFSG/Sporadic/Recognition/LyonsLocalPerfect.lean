module

public import CFSG.Sporadic.Recognition.LyonsLocalBasic
public import CFSG.Sporadic.Recognition.LyonsLocalThreeA
public import CFSG.Sporadic.Recognition.McLMultiplierCert
public import CFSG.Sporadic.Recognition.LyonsAS4NormQuot

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Blueprint
open scoped commutatorElement

section Quot

variable {G : Type*} [Group G] (x : G)

theorem mem_zpowers_of_mk_eq_one {m : ↥(centralizer ({x} : Set G))}
    (h : (QuotientGroup.mk m : CentQuot x) = 1) : (m : G) ∈ zpowers x := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ((QuotientGroup.eq_one_iff _).1 h)
  have := congrArg Subtype.val hk
  rw [Subgroup.coe_zpow] at this
  exact Subgroup.mem_zpowers_iff.2 ⟨k, this⟩

theorem mk_eq_one_of_mem_zpowers {m : ↥(centralizer ({x} : Set G))}
    (h : (m : G) ∈ zpowers x) : (QuotientGroup.mk m : CentQuot x) = 1 := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  rw [QuotientGroup.eq_one_iff]
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_zpow]
  exact hk

end Quot

@[expose] def c5p : Perm (Fin 11) := swap 6 7 * swap 7 8 * swap 8 9 * swap 9 10

theorem sign_c5p : sign c5p = 1 := by decide
theorem c5p_pow_five : c5p ^ 5 = 1 := by decide
theorem c5p_ne_one : c5p ≠ 1 := by decide
theorem c5p_comm_x1p : c5p * x1p = x1p * c5p := by decide
theorem c5p_comm_x2p : c5p * x2p = x2p * c5p := by decide

namespace IsCover11

variable {E : Type*} [Group E] {ρ : E →* Perm (Fin 11)} {z : E}

theorem exists_lift_pow_five (h : IsCover11 ρ z) {p : Perm (Fin 11)} (hp : sign p = 1)
    (hp5 : p ^ 5 = 1) : ∃ c : E, ρ c = p ∧ c ^ 5 = 1 := by
  obtain ⟨d, hd⟩ := h.exists_lift hp
  have hd5 : ρ (d ^ 5) = 1 := by rw [map_pow, hd, hp5]
  rcases h.mem_ker_iff.mp hd5 with h1 | h1
  · exact ⟨d, hd, h1⟩
  · refine ⟨d * z, by rw [h.rho_mul_z, hd], ?_⟩
    rw [Commute.mul_pow (h.mul_z_comm d), h1]
    have : z ^ 5 = z := by
      calc z ^ 5 = (z ^ 2) ^ 2 * z := by group
        _ = z := by rw [h.sq_eq_one]; group
    rw [this, h.z_mul_z]

end IsCover11

section Std

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

omit [Finite G] in
theorem comm₂₁ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    (x₂ : G) * (x₁ : G) = (x₁ : G) * (x₂ : G) := by
  have := congrArg Subtype.val
    (D.cover.commute_of_rho_commute_pow_three S.pow₁ (g := x₂)
      (by rw [S.rho₁, S.rho₂]; exact disjoint_x1p_x2p.commute.symm.eq))
  simpa using this

omit [Finite G] in
@[expose] def x₂M (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ↥(centralizer ({(x₁ : G)} : Set G)) :=
  ⟨(x₂ : G), mem_centralizer_singleton_iff.2 (D.comm₂₁ S)⟩

omit [Finite G] in
@[expose] def x₂Q (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) : CentQuot (x₁ : G) :=
  QuotientGroup.mk (D.x₂M S)

omit [Finite G] in
theorem orderOf_x₂Q (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) : orderOf (D.x₂Q S) = 3 := by
  have h3 : D.x₂Q S ^ 3 = 1 := by
    rw [x₂Q, ← QuotientGroup.mk_pow]
    have : D.x₂M S ^ 3 = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val S.pow₂
      simpa [x₂M] using this
    rw [this]; rfl
  have hne : D.x₂Q S ≠ 1 := by
    intro h1
    have h2 := mem_zpowers_of_mk_eq_one (x₁ : G) h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h2
    have hx1 : (x₁ : G) ^ k = ((x₁ ^ k : ↥(centralizer ({t} : Set G))) : G) := by
      rw [Subgroup.coe_zpow]
    have hH : x₁ ^ k = x₂ := Subtype.ext (hx1.symm.trans hk)
    have hX3 : x₁ ^ 3 = 1 := S.pow₁
    have hρ : ρ (x₁ ^ k) = x2p := by rw [hH, S.rho₂]
    rw [map_zpow, S.rho₁] at hρ
    rcases zpow_cases x1p_pow_three k with h | h | h
    · rw [h] at hρ; exact absurd hρ.symm (by decide)
    · rw [h] at hρ; exact absurd hρ.symm (by decide)
    · rw [h] at hρ; exact absurd hρ.symm (by decide)
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime h3 hne

omit [Finite G] in
theorem rho_zpow_ne_c5p (S : LyStd ρ x₁ x₂ x₃) (k : ℤ) : ρ (x₁ ^ k) ≠ c5p := by
  rw [map_zpow, S.rho₁]
  rcases zpow_cases x1p_pow_three k with h | h | h <;> rw [h] <;> decide

omit [Finite G] in
theorem five_dvd_card_centralizer_x₂Q (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    5 ∣ Nat.card ↥(centralizer ({D.x₂Q S} : Set (CentQuot (x₁ : G)))) := by
  obtain ⟨w, hwρ, hw5⟩ := D.cover.exists_lift_pow_five sign_c5p c5p_pow_five
  have hw₁ : w * x₁ = x₁ * w :=
    D.cover.commute_of_rho_commute_pow_three S.pow₁ (by rw [hwρ, S.rho₁]; exact c5p_comm_x1p)
  have hw₂ : w * x₂ = x₂ * w :=
    D.cover.commute_of_rho_commute_pow_three S.pow₂ (by rw [hwρ, S.rho₂]; exact c5p_comm_x2p)
  let wM : ↥(centralizer ({(x₁ : G)} : Set G)) :=
    ⟨(w : G), mem_centralizer_singleton_iff.2 (congrArg Subtype.val hw₁)⟩
  let q : CentQuot (x₁ : G) := QuotientGroup.mk wM
  have hq5 : q ^ 5 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : wM ^ 5 = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hw5
      simpa [wM] using this
    rw [this]; rfl
  have hqne : q ≠ 1 := by
    intro h1
    have h2 := mem_zpowers_of_mk_eq_one (x₁ : G) h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h2
    have hx1 : (x₁ : G) ^ k = ((x₁ ^ k : ↥(centralizer ({t} : Set G))) : G) := by
      rw [Subgroup.coe_zpow]
    have hH : x₁ ^ k = w := Subtype.ext (hx1.symm.trans hk)
    exact rho_zpow_ne_c5p S k (by rw [hH, hwρ])
  have hcomm : q * D.x₂Q S = D.x₂Q S * q := by
    rw [x₂Q, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have h := congrArg Subtype.val hw₂
    exact h
  have hqC : q ∈ centralizer ({D.x₂Q S} : Set (CentQuot (x₁ : G))) :=
    mem_centralizer_singleton_iff.2 hcomm
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf (⟨q, hqC⟩ : ↥(centralizer ({D.x₂Q S} : Set (CentQuot (x₁ : G))))) = 5 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hq5 hqne
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem commute_of_mk_commute (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    {m : ↥(centralizer ({(x₁ : G)} : Set G))}
    (h : (QuotientGroup.mk m : CentQuot (x₁ : G)) * D.x₂Q S =
      D.x₂Q S * QuotientGroup.mk m) :
    (m : G) * (x₂ : G) = (x₂ : G) * (m : G) := by
  apply D.commute_of_comm_mem_zpowers S
  have h1 := mem_zpowers_of_mk_eq_one (x₁ : G)
    (m := m * D.x₂M S * m⁻¹ * (D.x₂M S)⁻¹) (by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv]
      change (QuotientGroup.mk m : CentQuot (x₁ : G)) * D.x₂Q S * (QuotientGroup.mk m)⁻¹ *
        (D.x₂Q S)⁻¹ = 1
      rw [h]
      group)
  exact h1

omit [Finite G] in
theorem x₂_mem_Lsub (S : LyStd ρ x₁ x₂ x₃) : x₂ ∈ IsCover11.Lsub ρ := by
  rw [IsCover11.mem_Lsub, S.rho₂]
  exact mem_fix012.2 (by decide)

omit [Finite G] in
theorem x₂M_mem_commutator (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    D.x₂M S ∈ commutator ↥(centralizer ({(x₁ : G)} : Set G)) := by
  have hperf : commutator ↥(IsCover11.Lsub ρ) = ⊤ :=
    Group.isPerfect_def.mp (IsCover11.Lsub_isPerfect D.cover)
  have h1 : (⟨x₂, x₂_mem_Lsub S⟩ : ↥(IsCover11.Lsub ρ)) ∈ commutator ↥(IsCover11.Lsub ρ) := by
    rw [hperf]; exact mem_top _
  have h2 := Subgroup.mem_map_of_mem (D.toCent S.pow₁ S.rho₁) h1
  have h3 : (commutator ↥(IsCover11.Lsub ρ)).map (D.toCent S.pow₁ S.rho₁) ≤
      commutator ↥(centralizer ({(x₁ : G)} : Set G)) := by
    rw [commutator_def, Subgroup.map_commutator]
    exact commutator_mono le_top le_top
  exact h3 h2

end LyData

end Std

section Main

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

theorem exists_commutator_pair (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ∃ a b : ↥(centralizer ({(x₁ : G)} : Set G)),
      (a : G) * (x₂ : G) = (x₂ : G) * (a : G) ∧ (b : G) * (x₂ : G) = (x₂ : G) * (b : G) ∧
      ∃ j : ℤ, ((⁅a, b⁆ : ↥(centralizer ({(x₁ : G)} : Set G))) : G) =
        (x₂ : G) * (x₁ : G) ^ j := by
  obtain ⟨e⟩ := (D.centQuot_mcl S.pow₁ S.rho₁)
  have hy3 := D.orderOf_x₂Q S
  have hc := card_centralizer_eq_of_five_dvd e hy3 (D.five_dvd_card_centralizer_x₂Q S)
  obtain ⟨a', b', ha', hb', hab'⟩ := exists_commutator_of_card_eq e hy3 hc
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
  refine ⟨a, b, D.commute_of_mk_commute S ha', D.commute_of_mk_commute S hb', ?_⟩
  have hk : (QuotientGroup.mk ((D.x₂M S)⁻¹ * ⁅a, b⁆) : CentQuot (x₁ : G)) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h1 : (QuotientGroup.mk ⁅a, b⁆ : CentQuot (x₁ : G)) =
        ⁅(QuotientGroup.mk a : CentQuot (x₁ : G)), QuotientGroup.mk b⁆ :=
      map_commutatorElement (QuotientGroup.mk' _) a b
    rw [h1, hab']
    change (D.x₂Q S)⁻¹ * D.x₂Q S = 1
    group
  have h2 := mem_zpowers_of_mk_eq_one (x₁ : G) hk
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h2
  refine ⟨j, ?_⟩
  have hj' : (x₁ : G) ^ j = (x₂ : G)⁻¹ * ((⁅a, b⁆ : ↥(centralizer ({(x₁ : G)} : Set G))) : G) := hj
  rw [hj']
  group

theorem exists_x₁_mul_mem_commutator (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ∃ j : ℤ, (x₁ : G) * (x₂ : G) ^ j ∈
      (commutator ↥(centralizer ({(x₁ : G)} : Set G))).map
        (centralizer ({(x₁ : G)} : Set G)).subtype := by
  obtain ⟨a, b, ha, hb, j, hj⟩ := D.exists_commutator_pair S
  obtain ⟨s, hs₁, hs₂, -, -⟩ := D.exists_swap S
  have hsX : (s : G) * (x₁ : G) * (s : G)⁻¹ = (x₂ : G) := by
    have := congrArg Subtype.val hs₁; simpa using this
  have hsY : (s : G) * (x₂ : G) * (s : G)⁻¹ = (x₁ : G) := by
    have := congrArg Subtype.val hs₂; simpa using this
  have hconj : ∀ m : ↥(centralizer ({(x₁ : G)} : Set G)),
      (m : G) * (x₂ : G) = (x₂ : G) * (m : G) →
      (s : G) * (m : G) * (s : G)⁻¹ ∈ centralizer ({(x₁ : G)} : Set G) := by
    intro m hm
    rw [mem_centralizer_singleton_iff]
    have e1 : (s : G) * (m : G) * (s : G)⁻¹ * (x₁ : G) =
        (s : G) * ((m : G) * (x₂ : G)) * (s : G)⁻¹ := by
      calc (s : G) * (m : G) * (s : G)⁻¹ * (x₁ : G)
          = (s : G) * (m : G) * (s : G)⁻¹ * ((s : G) * (x₂ : G) * (s : G)⁻¹) := by rw [hsY]
        _ = (s : G) * ((m : G) * (x₂ : G)) * (s : G)⁻¹ := by group
    have e2 : (x₁ : G) * ((s : G) * (m : G) * (s : G)⁻¹) =
        (s : G) * ((x₂ : G) * (m : G)) * (s : G)⁻¹ := by
      calc (x₁ : G) * ((s : G) * (m : G) * (s : G)⁻¹)
          = ((s : G) * (x₂ : G) * (s : G)⁻¹) * ((s : G) * (m : G) * (s : G)⁻¹) := by rw [hsY]
        _ = (s : G) * ((x₂ : G) * (m : G)) * (s : G)⁻¹ := by group
    rw [e1, e2, hm]
  let a' : ↥(centralizer ({(x₁ : G)} : Set G)) := ⟨(s : G) * (a : G) * (s : G)⁻¹, hconj a ha⟩
  let b' : ↥(centralizer ({(x₁ : G)} : Set G)) := ⟨(s : G) * (b : G) * (s : G)⁻¹, hconj b hb⟩
  refine ⟨j, ⟨⁅a', b'⁆, ?_, ?_⟩⟩
  · rw [commutator_eq_closure]
    exact Subgroup.subset_closure ⟨a', b', rfl⟩
  · show ((⁅a', b'⁆ : ↥(centralizer ({(x₁ : G)} : Set G))) : G) = (x₁ : G) * (x₂ : G) ^ j
    have h1 : ((⁅a', b'⁆ : ↥(centralizer ({(x₁ : G)} : Set G))) : G) =
        (s : G) * ((⁅a, b⁆ : ↥(centralizer ({(x₁ : G)} : Set G))) : G) * (s : G)⁻¹ := by
      show ⁅(s : G) * (a : G) * (s : G)⁻¹, (s : G) * (b : G) * (s : G)⁻¹⁆ =
        (s : G) * ⁅(a : G), (b : G)⁆ * (s : G)⁻¹
      group
    rw [h1, hj]
    calc (s : G) * ((x₂ : G) * (x₁ : G) ^ j) * (s : G)⁻¹
        = ((s : G) * (x₂ : G) * (s : G)⁻¹) * ((s : G) * (x₁ : G) * (s : G)⁻¹) ^ j := by
          rw [conj_zpow]; group
      _ = (x₁ : G) * (x₂ : G) ^ j := by rw [hsX, hsY]

theorem x₁M_mem_commutator (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    (⟨(x₁ : G), self_mem_centralizer_singleton _⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) ∈
      commutator ↥(centralizer ({(x₁ : G)} : Set G)) := by
  obtain ⟨j, hj⟩ := D.exists_x₁_mul_mem_commutator S
  set Cm : Subgroup G := (commutator ↥(centralizer ({(x₁ : G)} : Set G))).map
    (centralizer ({(x₁ : G)} : Set G)).subtype with hCm
  have hY : (x₂ : G) ∈ Cm := Subgroup.mem_map_of_mem _ (D.x₂M_mem_commutator S)
  have hX : (x₁ : G) ∈ Cm := by
    have := Cm.mul_mem hj (Cm.zpow_mem hY (-j))
    simpa [zpow_neg, mul_assoc] using this
  obtain ⟨z, hz, hzX⟩ := hX
  have : z = ⟨(x₁ : G), self_mem_centralizer_singleton _⟩ := Subtype.ext hzX
  rw [← this]
  exact hz

theorem isPerfect_centralizer (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Group.IsPerfect ↥(centralizer ({(x₁ : G)} : Set G)) := by
  obtain ⟨hsimple, hnab, -⟩ := D.centQuot_facts S.pow₁ S.rho₁
  have hperfQ : commutator (CentQuot (x₁ : G)) = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (commutator (CentQuot (x₁ : G))) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have : ⁅a, b⁆ ∈ commutator (CentQuot (x₁ : G)) := by
        rw [commutator_eq_closure]; exact Subgroup.subset_closure ⟨a, b, rfl⟩
      rw [h, Subgroup.mem_bot, commutatorElement_def] at this
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [this]; group
    · exact h
  set π : ↥(centralizer ({(x₁ : G)} : Set G)) →* CentQuot (x₁ : G) := QuotientGroup.mk' _ with hπ
  have hker : π.ker = zpowers (⟨(x₁ : G), self_mem_centralizer_singleton _⟩ :
      ↥(centralizer ({(x₁ : G)} : Set G))) := QuotientGroup.ker_mk' _
  have hmap : (commutator ↥(centralizer ({(x₁ : G)} : Set G))).map π = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
    rw [← commutator_def]; exact hperfQ
  have hle : π.ker ≤ commutator ↥(centralizer ({(x₁ : G)} : Set G)) := by
    rw [hker, Subgroup.zpowers_le]
    exact D.x₁M_mem_commutator S
  have hcomap := Subgroup.comap_map_eq π (commutator ↥(centralizer ({(x₁ : G)} : Set G)))
  rw [hmap, Subgroup.comap_top, sup_eq_left.2 hle] at hcomap
  exact ⟨hcomap.symm⟩

end LyData

end Main

section Center

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

omit [Finite G] in
theorem zpowers_le_center_centralizer (x : G) :
    zpowers (⟨x, self_mem_centralizer_singleton x⟩ : ↥(centralizer ({x} : Set G))) ≤
      Subgroup.center ↥(centralizer ({x} : Set G)) :=
  zpowers_le.2 <| Subgroup.mem_center_iff.2 fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.1 y.2)

omit [Finite G] in
theorem orderOf_x₁ (S : LyStd ρ x₁ x₂ x₃) : orderOf (x₁ : G) = 3 := by
  have h3 : (x₁ : G) ^ 3 = 1 := by
    have := congrArg Subtype.val S.pow₁
    simpa using this
  have h1 : (x₁ : G) ≠ 1 := by
    intro h
    have : x₁ = 1 := Subtype.ext h
    have h2 := S.rho₁
    rw [this, map_one] at h2
    exact absurd h2 (by decide)
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime h3 h1

theorem center_centralizer (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G)) =
      zpowers (⟨(x₁ : G), self_mem_centralizer_singleton _⟩ :
        ↥(centralizer ({(x₁ : G)} : Set G))) := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hsimple, hnab, -⟩ := D.centQuot_facts S.pow₁ S.rho₁
    have hcenQ := center_eq_bot_of_simple hsimple hnab
    have hmem : (QuotientGroup.mk c : CentQuot (x₁ : G)) ∈ Subgroup.center (CentQuot (x₁ : G)) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hc m]
    rw [hcenQ, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff c).1 hmem
  · exact zpowers_le_center_centralizer _

theorem card_center_centralizer (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card ↥(Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G))) = 3 := by
  rw [D.center_centralizer S, Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_x₁ S]

end LyData

theorem exists_hom_of_quotient_equiv {M K' J : Type*} [Group M] [Group K'] [Group J]
    (N : Subgroup M) [N.Normal] (e : M ⧸ N ≃* K') (f : K' ≃* J) :
    ∃ q : M →* J, Function.Surjective q ∧ q.ker = N := by
  refine ⟨(f.toMonoidHom.comp e.toMonoidHom).comp (QuotientGroup.mk' N), ?_, ?_⟩
  · exact (f.surjective.comp e.surjective).comp (QuotientGroup.mk'_surjective N)
  · ext m
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      MulEquiv.coe_toMonoidHom]
    rw [map_eq_one_iff _ f.injective, map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]

end Center



section Cover

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

theorem nonempty_mulEquiv_mclCover (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nonempty (↥(centralizer ({(x₁ : G)} : Set G)) ≃* McLMultiplier.MclCover) := by
  obtain ⟨e⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  have : Group.IsPerfect ↥(centralizer ({(x₁ : G)} : Set G)) := D.isPerfect_centralizer S
  obtain ⟨q, hq, hkerq⟩ := @exists_hom_of_quotient_equiv ↥(centralizer ({(x₁ : G)} : Set G))
    CFSG.Blueprint.NativeSporadic.McL CFSG.Sporadic.McL.J _ inferInstance inferInstance
    (zpowers (⟨(x₁ : G), self_mem_centralizer_singleton _⟩ :
      ↥(centralizer ({(x₁ : G)} : Set G)))) _ e CFSG.Sporadic.McL.mclEquivJ
  have hker : q.ker ≤ Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G)) := by
    rw [hkerq]; exact zpowers_le_center_centralizer _
  have hcard : Nat.card q.ker = 3 := by
    rw [hkerq, Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_x₁ S]
  obtain ⟨φ, -⟩ := McLMultiplier.exists_mulEquiv_of_triple_cover_of_certificate q hq hker hcard
  exact ⟨φ.symm⟩

end LyData

end Cover

end CFSG.Sporadic.Recognition.LyonsSims
