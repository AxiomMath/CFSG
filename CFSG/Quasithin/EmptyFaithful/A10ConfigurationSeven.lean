module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationFive
public import CFSG.Quasithin.Background.A1a
public import CFSG.Quasithin.Background.OrderingMax

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT

variable {G : Type*} [Group G]

theorem normal_of_charTwo_abelian_sylow [Finite G] {H J X : Subgroup G} (hCT : CharTwo H)
    (hJH : IsSylowTwoOf J H) (hXH : X ≤ H ⊓ Subgroup.centralizer (H : Set G)) (hXJ : X ≤ J)
    (hab : ⁅J, J⁆ ≤ X) : H ≤ Subgroup.normalizer (J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXn : (X.subgroupOf H).Normal := by
    refine ⟨fun x hx h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hxc : (x : G) ∈ Subgroup.centralizer (H : Set G) := (hXH hx).2
    have : (h : G) * x = x * h := Subgroup.mem_centralizer_iff.mp hxc h h.2
    have e : (h : G) * x * (h : G)⁻¹ = x := by rw [this]; group
    show (h : G) * x * (h : G)⁻¹ ∈ X
    rw [e]
    exact hx
  have hA18 := centralizer_pCore_quotient_subgroupOf_le (p := 2) hXH hCT
  set Q := H ⧸ X.subgroupOf H with hQ
  set π : H →* Q := QuotientGroup.mk' (X.subgroupOf H) with hπ
  have hker : π.ker = X.subgroupOf H := QuotientGroup.ker_mk' _
  have hJ' : J.subgroupOf H ≥ π.ker := by
    rw [hker]
    exact fun x hx => Subgroup.mem_subgroupOf.2 (hXJ (Subgroup.mem_subgroupOf.1 hx))
  set J' : Subgroup Q := (J.subgroupOf H).map π with hJ'def
  have hJp : IsPGroup 2 (J.subgroupOf H) := hJH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hJH.1).symm
  have hJ'p : IsPGroup 2 J' := hJp.map π
  have hJ'idx : ¬ 2 ∣ J'.index := by
    rw [hJ'def, Subgroup.index_map_eq (J.subgroupOf H) (QuotientGroup.mk'_surjective _) hJ']
    exact hJH.2.2
  let S : Sylow 2 Q := hJ'p.toSylow hJ'idx
  have hS : (S : Subgroup Q) = J' := rfl
  have hcomm : ∀ x ∈ J', ∀ y ∈ J', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have ha' : (a : G) ∈ J := Subgroup.mem_subgroupOf.1 ha
    have hb' : (b : G) ∈ J := Subgroup.mem_subgroupOf.1 hb
    have := Subgroup.commutator_mem_commutator (J.inv_mem hb') (J.inv_mem ha')
    have h2 := hab this
    simpa [commutatorElement_def, mul_assoc] using h2
  have hpC : IsPGroup 2 (CFSG.Open.pCore 2 Q) := CFSG.pCore_isPGroup (p := 2)
  have hNc : (CFSG.Open.pCore 2 Q).Normal := CFSG.pCore_normal (p := 2)
  have hcore : CFSG.Open.pCore 2 Q ≤ J' := hpC.le_sylow_of_normal S
  have hJ'le : J' ≤ CFSG.Open.pCore 2 Q := by
    intro x hx
    apply hA18
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y (hcore hy)).symm
  have hJeq : J' = CFSG.Open.pCore 2 Q := le_antisymm hJ'le hcore
  have hJnormal : J'.Normal := hJeq ▸ hNc
  have hcomap : J'.comap π = J.subgroupOf H := Subgroup.comap_map_eq_self hJ'
  have : (J.subgroupOf H).Normal := hcomap ▸ hJnormal.comap π
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJH.1).1 this

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

theorem z_mem_centralizer_z : E.z ∈ Subgroup.centralizer ({E.z} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]

theorem t_mem_T : E.t ∈ T := E.mem_T_iff.2 ⟨t0, Jh_le_Th (T1h_le_Jh t0_mem_T1h), rfl⟩

theorem centralizer_pair_eq : Subgroup.centralizer ({E.z, E.t} : Set G) =
    Subgroup.centralizer ({E.z} : Set G) ⊓ Subgroup.centralizer ({E.t} : Set G) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

theorem charTwo_centralizer_z [Finite G] (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) : CharTwo (Subgroup.centralizer ({E.z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hzp : IsPGroup 2 (Subgroup.zpowers E.z) := isPGroup_zpowers_of_mul_self E.z_sq
  have hle : Subgroup.zpowers E.z ≤ Subgroup.centralizer ({E.z} : Set G) :=
    Subgroup.zpowers_le.2 E.z_mem_centralizer_z
  have hnorm : Subgroup.centralizer ({E.z} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers E.z : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have hc : E.z * g = g * E.z := Subgroup.mem_centralizer_iff.mp hg E.z rfl
    have key : ∀ x ∈ Subgroup.zpowers E.z, g * x * g⁻¹ = x := by
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hcom : Commute g E.z := hc.symm
      have := (hcom.zpow_right n).eq
      calc g * E.z ^ n * g⁻¹ = E.z ^ n * g * g⁻¹ := by rw [this]
        _ = E.z ^ n := by group
    intro x
    constructor
    · intro hx
      rw [key x hx]
      exact hx
    · intro hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hcom : Commute g E.z := hc.symm
      have h2 : g * E.z ^ n = E.z ^ n * g := (hcom.zpow_right n).eq
      have hx2 : x = E.z ^ n := by
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g⁻¹ * E.z ^ n * g := by rw [← hn]
          _ = g⁻¹ * (E.z ^ n * g) := by group
          _ = g⁻¹ * (g * E.z ^ n) := by rw [h2]
          _ = E.z ^ n := by group
      rw [hx2]
      exact Subgroup.zpow_mem_zpowers E.z n
  have hp : Subgroup.zpowers E.z ≤ pCoreOf 2 (Subgroup.centralizer ({E.z} : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 hle hnorm hzp
  refine charTwo_of_inH hEven S ⟨hS ▸ E.T_le_centralizer_z, ?_⟩
  intro h
  have := hp (Subgroup.mem_zpowers E.z)
  rw [h, Subgroup.mem_bot] at this
  exact E.z_ne_one this

theorem A_inf_B_eq_map : E.A ⊓ E.B = (A1 ⊓ A2).map E.ι := by
  unfold A B
  rw [← Subgroup.map_inf _ _ E.ι E.injective]

theorem t_mem_centralizer_z : E.t ∈ Subgroup.centralizer ({E.z} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact (E.z_central E.t_mem_T).symm

theorem lemma_13_9_7 [Finite G] (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) :
    Subgroup.centralizer ({E.z, E.t} : Set G) = E.J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer ({E.z, E.t} : Set G) with hH
  have hHeq : H = Subgroup.centralizer ({E.z} : Set G) ⊓ Subgroup.centralizer ({E.t} : Set G) :=
    hH.trans E.centralizer_pair_eq
  have hHt : H ≤ Subgroup.centralizer ({E.t} : Set G) := by
    rw [hHeq]; exact inf_le_right
  have hJz : E.J ≤ Subgroup.centralizer ({E.z} : Set G) := E.J_le_T.trans E.T_le_centralizer_z
  have hJH : E.J ≤ H := by
    rw [hHeq]; exact le_inf hJz E.J_le_centralizer_t
  have hCT : CharTwo H := by
    have h1 := E.charTwo_centralizer_z hEven hT
    have h2 : Subgroup.zpowers E.t ≤ Subgroup.centralizer ({E.z} : Set G) :=
      Subgroup.zpowers_le.2 E.t_mem_centralizer_z
    have h3 := CharTwo.inf_centralizer h1 h2 (isPGroup_zpowers_of_mul_self E.t_sq)
    have h4 : Subgroup.centralizer ({E.z} : Set G) ⊓
        Subgroup.centralizer ((Subgroup.zpowers E.t : Subgroup G) : Set G) = H := by
      rw [hHeq]
      congr 1
      ext g
      simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff,
        forall_eq]
      constructor
      · intro h
        exact h E.t (Subgroup.mem_zpowers E.t)
      · intro h x hx
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        have hcom : Commute E.t g := h
        exact (hcom.zpow_left n).eq
    rwa [h4] at h3
  have hSyl : IsSylowTwoOf E.J H := A4.isSylowTwoOf_mono (E.isSylowTwoOf_J hT hM) hJH hHt
  have hcommH : ∀ h ∈ H, h * E.z = E.z * h ∧ h * E.t = E.t * h := by
    intro h hh
    have := Subgroup.mem_centralizer_iff.mp hh
    exact ⟨(this E.z (Or.inl rfl)).symm, (this E.t (Or.inr rfl)).symm⟩
  have hXH : E.A ⊓ E.B ≤ H ⊓ Subgroup.centralizer (H : Set G) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · show x ∈ Subgroup.centralizer ({E.z, E.t} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rcases hh with rfl | rfl
      · exact E.A_commute _ E.z_mem_A x hx.1
      · exact E.A_commute _ E.t_mem_A x hx.1
    · rw [E.A_inf_B_eq_map] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      show E.ι w ∈ Subgroup.centralizer (H : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨hz, ht⟩ := hcommH h hh
      have hw' := AB_cases w (Subgroup.mem_inf.1 hw).1 (Subgroup.mem_inf.1 hw).2
      rcases hw' with rfl | rfl | rfl | rfl
      · rw [map_one, mul_one, one_mul]
      · exact ht
      · rw [t0'_eq_mul, map_mul]
        change h * (E.t * E.z) = (E.t * E.z) * h
        rw [← mul_assoc, ht, mul_assoc, hz, ← mul_assoc]
      · exact hz
  have hXJ : E.A ⊓ E.B ≤ E.J := fun x hx => E.A_le_J hx.1
  have hab : ⁅E.J, E.J⁆ ≤ E.A ⊓ E.B := by
    have h1 : ⁅E.J, E.J⁆ = (⁅Jh, Jh⁆).map E.ι := (Subgroup.map_commutator Jh Jh E.ι).symm
    rw [h1, E.A_inf_B_eq_map]
    exact Subgroup.map_mono commutator_Jh_le_A1_inf_A2
  have hnorm := normal_of_charTwo_abelian_sylow hCT hSyl hXH hXJ hab
  have hHT : H ≤ T := by
    rw [← E.normalizer_J_eq hT hM]
    exact hnorm
  refine le_antisymm (fun y hy => ?_) hJH
  obtain ⟨w, hw, rfl⟩ := E.mem_T_iff.1 (hHT hy)
  have hc : w * t0 = t0 * w := E.injective (by
    rw [map_mul, map_mul]
    exact (hcommH _ hy).2)
  exact ⟨w, centralizer_t0_Th w hw hc, rfl⟩

end Emb

end CFSG.Quasithin.A10
