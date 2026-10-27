module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119SVec
public import CFSG.RankThree.PartTwo.Sec21.Hering2119SLin
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQ

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Module

section Sub

variable {G : Type*} [Group G] (D : Subgroup G) [Fact (IsElem3 D)]

@[expose] def Vec.addSub (M : Subgroup G) : AddSubgroup (Vec D) where
  carrier := {v | ((Vec.toD v : D) : G) ∈ M}
  zero_mem' := by
    show ((Vec.toD (0 : Vec D) : D) : G) ∈ M
    rw [Vec.toD_zero]; exact M.one_mem
  add_mem' := by
    intro v w hv hw
    show ((Vec.toD (v + w) : D) : G) ∈ M
    rw [Vec.toD_add]; exact M.mul_mem hv hw
  neg_mem' := by
    intro v hv
    show ((Vec.toD (-v) : D) : G) ∈ M
    rw [Vec.toD_neg]; exact M.inv_mem hv

@[expose] def Vec.sub (M : Subgroup G) : Submodule F3 (Vec D) :=
  (AddSubgroup.toZModSubmodule 3) (Vec.addSub D M)

end Sub

section Lift

theorem isPGroup_zpowers_of_pow_three {T : Type*} [Group T] {t : T} (ht : t ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers t) := by
  intro g
  obtain ⟨x, hx⟩ : ∃ x, x ∈ Subgroup.zpowers t ∧ x = (g : T) := ⟨g, g.2, rfl⟩
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, ht, one_zpow]
  rfl

theorem exists_pgroup_lift {N Γ : Type} [Group N] [Finite N] [Group Γ] (ρ : N →* Γ)
    (X : Subgroup Γ) (hXr : X ≤ ρ.range) (hX3 : IsPGroup 3 X) (e : N) (he : ρ e ∈ X)
    (he3 : e ^ 3 = 1) :
    ∃ S : Subgroup N, IsPGroup 3 S ∧ e ∈ S ∧ (∀ s ∈ S, ρ s ∈ X) ∧
      Nat.card X * Nat.card (S ⊓ ρ.ker : Subgroup N) ≤ Nat.card S := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T : Subgroup N := X.comap ρ with hT
  have heT : e ∈ T := he
  have hkerT : ρ.ker ≤ T := fun k hk => by
    show ρ k ∈ X
    rw [MonoidHom.mem_ker.mp hk]; exact X.one_mem
  let eT : T := ⟨e, heT⟩
  have heT3 : eT ^ 3 = 1 := Subtype.ext (by simpa using he3)
  obtain ⟨Q, hQ⟩ := (isPGroup_zpowers_of_pow_three heT3).exists_le_sylow
  let S : Subgroup N := (Q : Subgroup T).map T.subtype
  have hS3 : IsPGroup 3 S := Q.isPGroup'.map _
  have heS : e ∈ S := ⟨eT, hQ (Subgroup.mem_zpowers eT), rfl⟩
  have hSX : ∀ s ∈ S, ρ s ∈ X := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  refine ⟨S, hS3, heS, hSX, ?_⟩
  let π : T →* X := (ρ.comp T.subtype).codRestrict X (fun t => t.2)
  have hπsurj : Function.Surjective π := by
    rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := hXr hx
    exact ⟨⟨n, show ρ n ∈ X from hn ▸ hx⟩, Subtype.ext hn⟩
  have hker : Nat.card π.ker = Nat.card ρ.ker := by
    refine Nat.card_congr
      { toFun := fun k => ⟨(k.1 : N), by
          have := k.2
          rw [MonoidHom.mem_ker] at this ⊢
          have h2 := congrArg Subtype.val this
          exact h2⟩
        invFun := fun k => ⟨⟨k.1, hkerT k.2⟩, by
          rw [MonoidHom.mem_ker]
          exact Subtype.ext (MonoidHom.mem_ker.mp k.2)⟩
        left_inv := fun k => rfl
        right_inv := fun k => rfl }
  have hTcard : Nat.card T = Nat.card ρ.ker * Nat.card X := by
    rw [← hker]
    exact (Subgroup.card_ker_mul_card_of_surjective hπsurj).symm
  haveI : Finite ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  haveI : Finite X := Finite.of_injective (fun x : X => (⟨x, hXr x.2⟩ : ρ.range)) (by
    intro a b h
    have := congrArg Subtype.val h
    exact Subtype.ext this)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hX3
  have hSc : Nat.card S = 3 ^ (Nat.card T).factorization 3 := by
    rw [Subgroup.card_map_of_injective T.subtype_injective]
    exact Sylow.card_eq_multiplicity Q
  have hker0 : Nat.card ρ.ker ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card T).factorization 3 = (Nat.card ρ.ker).factorization 3 + n := by
    rw [hTcard, hn, Nat.factorization_mul hker0 (pow_ne_zero _ (by norm_num)),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  have hinf : Nat.card (S ⊓ ρ.ker : Subgroup N) ≤ 3 ^ (Nat.card ρ.ker).factorization 3 :=
    Item2119End6Proof.card_le_three_pow_of_isPGroup inf_le_right (hS3.to_inf_left)
  rw [hSc, hfac, hn, pow_add]
  calc 3 ^ n * Nat.card (S ⊓ ρ.ker : Subgroup N)
      ≤ 3 ^ n * 3 ^ (Nat.card ρ.ker).factorization 3 := Nat.mul_le_mul_left _ hinf
    _ = 3 ^ (Nat.card ρ.ker).factorization 3 * 3 ^ n := mul_comm _ _

end Lift

section NAGroup

variable {G : Type} [Group G] [Finite G]

theorem na_group {D M Y : Subgroup G} {e y d : G}
    (hD : IsElem3 D) (hD81 : Nat.card D = 81)
    (hMD : M ≤ D) (hM9 : Nat.card M = 9)
    (heN : e ∈ Subgroup.normalizer (D : Set G)) (he3 : e ^ 3 = 1)
    (hYN : Y ≤ Subgroup.normalizer (D : Set G)) (heY : e ∈ Y)
    (hεM : ∀ x ∈ D, e * x * e⁻¹ * x⁻¹ ∈ M)
    (hkerM : ∀ x ∈ D, e * x * e⁻¹ * x⁻¹ = 1 → x ∈ M)
    (hMc : ∀ m ∈ M, e * m * e⁻¹ = m)
    (hcent : ∀ w ∈ Y, ∃ h ∈ M, w * e * w⁻¹ = e * h)
    (hMY : ∀ w ∈ Y, ∀ m ∈ M, w * m * w⁻¹ ∈ M)
    (htrans : ∀ v ∈ M, ∀ w ∈ M, v ≠ 1 → w ≠ 1 → ∃ m ∈ Y, m * v * m⁻¹ = w)
    (hq : ∃ q ∈ Y, q ^ 3 = 1 ∧ ∃ m ∈ M, q * m * q⁻¹ ≠ m)
    (hyN : y ∈ Subgroup.normalizer (D : Set G)) (hyK : y ∉ Subgroup.centralizer (D : Set G))
    (hyD : ∀ x ∈ D, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers d) (hdM : d ∈ M) (hd1 : d ≠ 1)
    (hye : y * e * y⁻¹ * e⁻¹ ∈ Subgroup.centralizer (D : Set G))
    (hbound : ∀ X : Subgroup G, IsPGroup 3 X → e ∈ X →
      (∀ x ∈ X, x * e * x⁻¹ * e⁻¹ ∈ Subgroup.centralizer (D : Set G)) →
        Nat.card X ≤ Nat.card (X ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) * 81) :
    False := by
  classical
  haveI : Fact (IsElem3 D) := ⟨hD⟩
  haveI : Finite (Vec D) := inferInstanceAs (Finite (Additive D))
  set N : Subgroup G := Subgroup.normalizer (D : Set G) with hNdef
  let ρ : N →* (Vec D ≃ₗ[F3] Vec D) := conjLinHom D
  let eN : N := ⟨e, heN⟩
  let u₁ : Vec D ≃ₗ[F3] Vec D := ρ eN
  let ε : Vec D →ₗ[F3] Vec D := (u₁ : Vec D →ₗ[F3] Vec D) - LinearMap.id
  have hu₁ : ∀ v, u₁ v = v + ε v := by
    intro v
    simp [ε]
  have toD_ε : ∀ v : Vec D, ((Vec.toD (ε v) : D) : G) =
      e * (Vec.toD v : D) * e⁻¹ * ((Vec.toD v : D) : G)⁻¹ := by
    intro v
    have : ε v = u₁ v + -v := by simp [ε, sub_eq_add_neg]
    rw [this, Vec.toD_add, Vec.toD_neg]
    rfl
  let Mv : Submodule F3 (Vec D) := Vec.sub D M
  have hmemMv : ∀ v : Vec D, v ∈ Mv ↔ ((Vec.toD v : D) : G) ∈ M := fun v => Iff.rfl
  have hker : ∀ v, ε v = 0 ↔ v ∈ Mv := by
    intro v
    rw [hmemMv]
    have hv := (Vec.toD v).2
    constructor
    · intro h0
      apply hkerM _ hv
      rw [← toD_ε v, h0, Vec.toD_zero]
      rfl
    · intro hm
      apply Vec.toD_injective
      apply Subtype.ext
      rw [toD_ε v, Vec.toD_zero]
      have := hMc _ hm
      rw [this]
      simp
  have hrange_le : LinearMap.range ε ≤ Mv := by
    rintro _ ⟨v, rfl⟩
    rw [hmemMv, toD_ε]
    exact hεM _ (Vec.toD v).2
  have hMv9 : Nat.card Mv = 9 := by
    rw [← hM9]
    exact Nat.card_congr
      { toFun := fun v => ⟨((Vec.toD v.1 : D) : G), v.2⟩
        invFun := fun m => ⟨Vec.ofD ⟨m.1, hMD m.2⟩, m.2⟩
        left_inv := fun v => rfl
        right_inv := fun m => rfl }
  have hkercard : Nat.card (LinearMap.ker ε) = 9 := by
    rw [← hMv9]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by rw [LinearMap.mem_ker, hker v])
  have hVcard : Nat.card (Vec D) = 81 := by
    rw [← hD81]
    exact Nat.card_congr (Additive.toMul)
  have hrange9 : Nat.card (LinearMap.range ε) = 9 := by
    have h := AddSubgroup.card_ker_mul_card_range ε.toAddMonoidHom
    have h1 : Nat.card (ε.toAddMonoidHom).ker = 9 := by
      rw [← hkercard]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by
        rw [LinearMap.mem_ker]; rfl)
    have h2 : Nat.card (ε.toAddMonoidHom).range = Nat.card (LinearMap.range ε) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => by
        rw [LinearMap.mem_range]; rfl)
    rw [h1, h2, hVcard] at h
    omega
  have hrange_eq : LinearMap.range ε = Mv := by
    have h := AddSubgroup.eq_of_le_of_card_ge (H := (LinearMap.range ε).toAddSubgroup)
      (K := Mv.toAddSubgroup) hrange_le (by
        show Nat.card Mv ≤ Nat.card (LinearMap.range ε)
        rw [hMv9, hrange9])
    exact Submodule.toAddSubgroup_injective h
  have hε : ∀ v, ε (ε v) = 0 := fun v => (hker _).mpr (hrange_eq ▸ LinearMap.mem_range_self ε v)
  have hkerW : ∀ v, ε v = 0 → v ∈ LinearMap.range ε := fun v hv => hrange_eq ▸ (hker v).mp hv
  have hmemR : ∀ v, v ∈ LinearMap.range ε ↔ ((Vec.toD v : D) : G) ∈ M := by
    intro v; rw [hrange_eq]; exact hmemMv v
  let yN : N := ⟨y, hyN⟩
  let H : Subgroup (Vec D ≃ₗ[F3] Vec D) :=
    Subgroup.closure (ρ '' {n : N | (n : G) ∈ Y} ∪ {ρ yN})
  have hρY : ∀ n : N, (n : G) ∈ Y → ρ n ∈ H := fun n hn =>
    Subgroup.subset_closure (Or.inl ⟨n, hn, rfl⟩)
  have hρy : ρ yN ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have hu₁H : u₁ ∈ H := hρY eN heY
  have hρker : ∀ n : N, (n : G) ∈ Subgroup.centralizer (D : Set G) → ρ n = 1 := fun n hn =>
    (conjLinHom_eq_one_iff D n).mpr hn
  have hcentH : H ≤ Subgroup.centralizer {u₁} := by
    rw [Subgroup.closure_le]
    rintro _ (⟨n, hn, rfl⟩ | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨h, hhM, hw⟩ := hcent n hn
      have hhD : h ∈ D := hMD hhM
      let hN : N := ⟨h, Subgroup.le_normalizer hhD⟩
      have hhC : ρ hN = 1 := hρker hN (Subgroup.mem_centralizer_iff.mpr fun x hx =>
        hD.comm x hx h hhD)
      have e1 : n * eN = eN * hN * n := by
        apply Subtype.ext
        change (n : G) * e = e * h * (n : G)
        rw [← hw]
        group
      calc ρ n * u₁ = ρ (n * eN) := by rw [map_mul]
        _ = ρ (eN * hN * n) := by rw [e1]
        _ = u₁ * ρ n := by rw [map_mul, map_mul, hhC, mul_one]
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hkN : ρ (yN * eN * yN⁻¹ * eN⁻¹) = 1 := hρker _ hye
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hkN
      change ρ yN * u₁ * (ρ yN)⁻¹ * u₁⁻¹ = 1 at hkN
      have h2 := mul_inv_eq_one.mp hkN
      have h3 := mul_inv_eq_iff_eq_mul.mp h2
      exact h3
  have hcommH : ∀ h ∈ H, ∀ v, h (ε v) = ε (h v) := by
    intro h hh v
    have := Subgroup.mem_centralizer_singleton_iff.mp (hcentH hh)
    have hv : u₁ (h v) = h (u₁ v) := by
      have := congrArg (fun f : Vec D ≃ₗ[F3] Vec D => f v) this
      exact this.symm
    simp only [ε, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, map_sub]
    rw [hv]
  have htransV : ∀ w w' : Vec D, w ∈ LinearMap.range ε → w' ∈ LinearMap.range ε → w ≠ 0 →
      w' ≠ 0 → ∃ h ∈ H, h w = w' := by
    intro w w' hw hw' hw0 hw'0
    have hwM := (hmemR w).mp hw
    have hw'M := (hmemR w').mp hw'
    have hw1 : ((Vec.toD w : D) : G) ≠ 1 := fun h => hw0 (by
      apply Vec.toD_injective
      rw [Vec.toD_zero]
      exact Subtype.ext h)
    have hw'1 : ((Vec.toD w' : D) : G) ≠ 1 := fun h => hw'0 (by
      apply Vec.toD_injective
      rw [Vec.toD_zero]
      exact Subtype.ext h)
    obtain ⟨m, hmY, hmw⟩ := htrans _ hwM _ hw'M hw1 hw'1
    refine ⟨ρ ⟨m, hYN hmY⟩, hρY _ hmY, ?_⟩
    apply Vec.toD_injective
    apply Subtype.ext
    rw [toD_conjLinHom]
    exact hmw
  have hord3V : ∃ s ∈ H, s ^ 3 = 1 ∧ ∃ w ∈ LinearMap.range ε, s w ≠ w := by
    obtain ⟨q, hqY, hq3, m, hmM, hqm⟩ := hq
    refine ⟨ρ ⟨q, hYN hqY⟩, hρY _ hqY, ?_, Vec.ofD ⟨m, hMD hmM⟩, ?_, ?_⟩
    · rw [← map_pow]
      have : (⟨q, hYN hqY⟩ : N) ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hq3
      rw [this, map_one]
    · exact (hmemR _).mpr hmM
    · intro h
      apply hqm
      have := congrArg (fun v : Vec D => ((Vec.toD v : D) : G)) h
      change q * m * q⁻¹ = m at this
      exact this
  have hdD : d ∈ D := hMD hdM
  let d' : Vec D := Vec.ofD ⟨d, hdD⟩
  have hd'R : d' ∈ LinearMap.range ε := (hmemR _).mpr hdM
  have hd'0 : d' ≠ 0 := fun h => hd1 (by
    have := congrArg (fun v : Vec D => ((Vec.toD v : D) : G)) h
    exact this)
  have hτ_mem : ∀ v : Vec D, ρ yN v - v ∈ Submodule.span F3 {d'} := by
    intro v
    have hx : ((Vec.toD v : D) : G) ∈ D := (Vec.toD v).2
    have h1 : ((Vec.toD (ρ yN v - v) : D) : G) =
        y * (Vec.toD v : D) * y⁻¹ * ((Vec.toD v : D) : G)⁻¹ := by
      rw [sub_eq_add_neg, Vec.toD_add, Vec.toD_neg]
      rfl
    have h2 : y * (Vec.toD v : D) * y⁻¹ * ((Vec.toD v : D) : G)⁻¹ =
        (((Vec.toD v : D) : G) * y * ((Vec.toD v : D) : G)⁻¹ * y⁻¹)⁻¹ := by group
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.inv_mem _ (hyD _ hx))
    rw [Submodule.mem_span_singleton]
    refine ⟨(k : F3), ?_⟩
    apply Vec.toD_injective
    apply Subtype.ext
    rw [Int.cast_smul_eq_zsmul, h1, h2, ← hk]
    rfl
  have hτ1 : ρ yN ≠ 1 := fun h => hyK ((conjLinHom_eq_one_iff D yN).mp h)
  obtain ⟨X, hXH, hX3, hX243, hu₁X, hXcomm⟩ :=
    na_core ε hε hrange9 hkerW H hcommH u₁ hu₁ hu₁H htransV hord3V (ρ yN) hρy d' hd'R hd'0
      hτ_mem hτ1
  have hHr : H ≤ ρ.range := by
    rw [Subgroup.closure_le]
    rintro _ (⟨n, -, rfl⟩ | rfl)
    · exact ⟨n, rfl⟩
    · exact ⟨yN, rfl⟩
  obtain ⟨S, hS3, heS, hSX, hcard⟩ := exists_pgroup_lift ρ X (hXH.trans hHr) hX3 eN hu₁X
    (Subtype.ext (by simpa using he3))
  let S' : Subgroup G := S.map N.subtype
  have hS'3 : IsPGroup 3 S' := hS3.map _
  have heS' : e ∈ S' := ⟨eN, heS, rfl⟩
  have hS'comm : ∀ x ∈ S', x * e * x⁻¹ * e⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := hXcomm _ (hSX t ht)
    have h2 : ρ (t * eN * t⁻¹ * eN⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      change ρ t * u₁ * (ρ t)⁻¹ * u₁⁻¹ = 1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact h1
    exact (conjLinHom_eq_one_iff D _).mp h2
  have hb := hbound S' hS'3 heS' hS'comm
  have hkerS : (S' ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) =
      (S ⊓ ρ.ker : Subgroup N).map N.subtype := by
    ext g
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hg⟩
      exact ⟨t, ⟨ht, (conjLinHom_eq_one_iff D t).mpr hg⟩, rfl⟩
    · rintro ⟨t, ⟨ht, htk⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, (conjLinHom_eq_one_iff D t).mp htk⟩
  have hc1 : Nat.card S' = Nat.card S := Subgroup.card_map_of_injective N.subtype_injective
  have hc2 : Nat.card (S' ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) =
      Nat.card (S ⊓ ρ.ker : Subgroup N) := by
    rw [hkerS]
    exact Subgroup.card_map_of_injective N.subtype_injective
  rw [hc1, hc2] at hb
  have hpos : 0 < Nat.card (S ⊓ ρ.ker : Subgroup N) := Nat.card_pos
  have h1 : 243 * Nat.card (S ⊓ ρ.ker : Subgroup N) ≤ Nat.card S :=
    (Nat.mul_le_mul_right _ hX243).trans hcard
  omega

end NAGroup

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
