module

public import CFSG.RankThree.CentralLift.LinearSplitting
public import CFSG.RankThree.PerfectCover.AbelianRadicalDilation

public section

namespace CFSG.RankThree.CentralLift

open Matrix

theorem existsUnique_lift_specialLinear {p ℓ f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hf : 1 ≤ f) {k : Type} [Field k] (hk : Nat.card k = ℓ ^ f) {n : ℕ}
    (hn : 2 ≤ n) {E G : Type*} [Group E] [Group G] [Finite E] (π : E →* G)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker)
    (α : SpecialLinearGroup (Fin n) k →* G) :
    ∃! β : SpecialLinearGroup (Fin n) k →* E, π.comp β = α := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero f hℓ.ne_zero)
  have : Fintype k := Fintype.ofFinite k
  set P := (α.comp (MonoidHom.fst _ E)).eqLocus (π.comp (MonoidHom.snd _ E)) with hP
  set ρ := (MonoidHom.fst _ E).comp P.subtype with hρ
  have hmemP : ∀ y : SpecialLinearGroup (Fin n) k × E, y ∈ P ↔ α y.1 = π y.2 := fun _ =>
    Iff.rfl
  have hρs : Function.Surjective ρ := by
    intro x
    obtain ⟨e, he⟩ := hπ (α x)
    exact ⟨⟨(x, e), (hmemP _).2 he.symm⟩, rfl⟩
  have hρker : ∀ y : P, y ∈ ρ.ker ↔ (y : SpecialLinearGroup (Fin n) k × E).1 = 1 :=
    fun _ => Iff.rfl
  have hkerπ : ∀ y : P, y ∈ ρ.ker → (y : SpecialLinearGroup (Fin n) k × E).2 ∈ π.ker := by
    intro y hy
    rw [MonoidHom.mem_ker, ← (hmemP _).1 y.2, (hρker y).1 hy, map_one]
  have hA : ρ.ker ≤ Subgroup.center P := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    have hc := Subgroup.mem_center_iff.1 (hC (hkerπ y hy))
      (z : SpecialLinearGroup (Fin n) k × E).2
    have h1 : (y : SpecialLinearGroup (Fin n) k × E).1 = 1 := (hρker y).1 hy
    refine Subtype.ext (Prod.ext ?_ hc)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Prod.fst_mul, Prod.fst_mul, h1, mul_one, one_mul]
  have hAp : IsPGroup p ρ.ker := by
    refine hCp.of_injective
      ((MonoidHom.snd _ E).comp (P.subtype.comp ρ.ker.subtype) |>.codRestrict π.ker
        fun y => hkerπ y y.2) fun y z hyz => ?_
    have h2 : (y : P).1.2 = (z : P).1.2 := congrArg Subtype.val hyz
    exact Subtype.ext (Subtype.ext (Prod.ext (((hρker y).1 y.2).trans ((hρker z).1 z.2).symm)
      h2))
  obtain ⟨⟨σ, hσ, hσu⟩, -⟩ :=
    LinearRoots.odd_field_linear_central_large_prime_extension_splitting hp hp3 hℓ hℓodd hf hk
      hn ρ hρs hA hAp
  have hsec : ∀ β : SpecialLinearGroup (Fin n) k →* E, π.comp β = α →
      ∃ σ₁ : SpecialLinearGroup (Fin n) k →* P, ρ.comp σ₁ = MonoidHom.id _ ∧
        (MonoidHom.snd _ E).comp (P.subtype.comp σ₁) = β := by
    intro β hβ
    refine ⟨((MonoidHom.id _).prod β).codRestrict P fun x => ?_, ?_, ?_⟩
    · rw [hmemP]
      exact (DFunLike.congr_fun hβ x).symm
    · ext x
      rfl
    · ext x
      rfl
  refine ⟨(MonoidHom.snd _ E).comp (P.subtype.comp σ), ?_, fun β hβ => ?_⟩
  · ext x
    have hx := DFunLike.congr_fun hσ x
    change ((σ x : P) : SpecialLinearGroup (Fin n) k × E).1 = x at hx
    change π ((σ x : P) : SpecialLinearGroup (Fin n) k × E).2 = α x
    rw [← (hmemP _).1 (σ x).2, hx]
  · obtain ⟨σ₁, hσ₁, rfl⟩ := hsec β hβ
    rw [hσu σ₁ hσ₁]

theorem exists_coprime_lift {E S : Type*} [Group E] [Group S] [Finite E] {p : ℕ}
    (hp : p.Prime) (π : E →* S) (hπ : Function.Surjective π) {d : S}
    (hd : Nat.Coprime (orderOf d) p) :
    ∃ a : E, π a = d ∧ Nat.Coprime (orderOf a) p := by
  by_cases hd1 : d = 1
  · exact ⟨1, by rw [hd1, map_one], by rw [orderOf_one]; exact Nat.coprime_one_left p⟩
  obtain ⟨e, rfl⟩ := hπ d
  have he0 : orderOf e ≠ 0 := (orderOf_pos e).ne'
  have hdo : 1 < orderOf (π e) := by
    have h0 : orderOf (π e) ≠ 0 := fun h0 => he0 (Nat.eq_zero_of_zero_dvd
      (h0 ▸ orderOf_map_dvd π e))
    have h1 : orderOf (π e) ≠ 1 := fun h1 => hd1 (orderOf_eq_one_iff.1 h1)
    omega
  obtain ⟨k₀, m, hm, hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd he0 p hp.ne_one
  have hmp : Nat.Coprime m p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (Nat.Coprime.pow_left k₀ (Nat.coprime_comm.1 hd)) hdo
  refine ⟨e ^ (p ^ k₀ * u), ?_, ?_⟩
  · rw [map_pow, ← pow_mod_orderOf, hu, pow_one]
  · have hpow : (e ^ (p ^ k₀ * u)) ^ m = 1 := by
      rw [← pow_mul, show p ^ k₀ * u * m = p ^ k₀ * m * u by ring, pow_mul, ← hem,
        pow_orderOf_eq_one, one_pow]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hpow) hmp

section Dilation

variable {E S : Type*} [Group E] [Group S]

theorem mem_normalizer_of_conj_mem [Finite S] {H : Subgroup S} {g : S}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set S) := by
  let φ : H → H := fun x => ⟨g * x * g⁻¹, h x x.2⟩
  have hφ : Function.Injective φ := fun x y hxy => by
    have h1 : g * (x : S) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hφs := Finite.surjective_of_injective hφ
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  obtain ⟨x, hx⟩ := hφs ⟨g * y * g⁻¹, hy⟩
  have hxy : (x : S) = y := by
    have h1 : g * (x : S) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hx
    exact mul_left_cancel (mul_right_cancel h1)
  exact hxy ▸ x.2

theorem mem_normalizer_comap (π : E →* S) {H : Subgroup S} {g : E}
    (hg : π g ∈ Subgroup.normalizer (H : Set S)) :
    g ∈ Subgroup.normalizer ((H.comap π : Subgroup E) : Set E) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  have h := hg (π x)
  simp only [Subgroup.mem_comap, map_mul, map_inv] at h ⊢
  exact h

variable [Finite E] [Group.IsPerfect E] {p : ℕ} [Fact p.Prime]

theorem ker_eq_bot_of_radical_dilation (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) (R V : Subgroup S)
    (hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (hRpow : ∀ x ∈ R, x ^ p = 1)
    (hRab : ∀ x ∈ R.comap π, ∀ y ∈ R.comap π, x * y = y * x)
    (hRV : R ⊓ V = ⊥) (hVR : V ≤ Subgroup.normalizer (R : Set S))
    (hSyl : ∃ P : Sylow p S, (P : Subgroup S) = R ⊔ V) (Vh : Subgroup E)
    (hVh : Vh.map π = V) (hVhinj : π.ker ⊓ Vh = ⊥) (a : E) (hacop : Nat.Coprime (orderOf a) p)
    (haVh : a ∈ Subgroup.centralizer (Vh : Set E)) (ℓ : (ZMod p)ˣ) (hℓ : ℓ ≠ 1)
    (haR : ∀ x ∈ R, π a * x * (π a)⁻¹ = x ^ (ℓ : ZMod p).val) : π.ker = ⊥ := by
  have : Finite S := Finite.of_surjective π hπ
  obtain ⟨P₀, hP₀⟩ := hSyl
  set P : Sylow p E := P₀.comapOfKerIsPGroup π hCp (by
    rw [MonoidHom.range_eq_top.2 hπ]
    exact le_top) with hPdef
  have hPc : (P : Subgroup E) = (R ⊔ V).comap π := by
    rw [hPdef, Sylow.coe_comapOfKerIsPGroup, hP₀]
  have haV : ∀ v ∈ V, π a * v * (π a)⁻¹ = v := by
    intro v hv
    rw [← hVh] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [← map_inv, ← map_mul, ← map_mul, ← Subgroup.mem_centralizer_iff.1 haVh w hw,
      mul_inv_cancel_right]
  have haRn : π a ∈ Subgroup.normalizer (R : Set S) :=
    mem_normalizer_of_conj_mem fun x hx => by
      rw [haR x hx]
      exact pow_mem hx _
  have hRVn : R ⊔ V ≤ Subgroup.normalizer (R : Set S) := sup_le Subgroup.le_normalizer hVR
  have haRV : π a ∈ Subgroup.normalizer ((R ⊔ V : Subgroup S) : Set S) := by
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have hle : R ⊔ V ≤ (R ⊔ V).comap (MulAut.conj (π a)).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 haRn y).1 hy)
      · change π a * y * (π a)⁻¹ ∈ R ⊔ V
        rw [haV y hy]
        exact Subgroup.mem_sup_right hy
    exact hle hx
  set Rt := R.comap π with hRt
  have hRtP : Rt ≤ P := by
    rw [hPc]
    exact Subgroup.comap_mono le_sup_left
  have hVhP : Vh ≤ P := by
    rw [hPc]
    intro x hx
    exact Subgroup.mem_sup_right (hVh ▸ Subgroup.mem_map_of_mem π hx)
  have hRtab : IsMulCommutative Rt :=
    ⟨⟨fun x y => Subtype.ext (hRab x x.2 y y.2)⟩⟩
  have hCRt : π.ker ≤ Rt := fun x hx => by
    rw [hRt, Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact one_mem _
  let πR : Rt →* R := (π.comp Rt.subtype).codRestrict R fun x => x.2
  have hπR : Function.Surjective πR := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hπRker : πR.ker = π.ker.subgroupOf Rt := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hW : CFSG.IsElementaryAbelian p R :=
    { is_comm := ⟨fun x y => Subtype.ext (hRcomm x x.2 y y.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, hRpow x x.2, Subgroup.coe_one]) }
  have hRn : (P : Subgroup E) ≤ Subgroup.normalizer (Rt : Set E) := by
    intro x hx
    rw [hPc] at hx
    exact mem_normalizer_comap π (hRVn hx)
  have hRtVh : Rt ⊓ Vh = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have h1 : π x ∈ R ⊓ V := ⟨hx1, hVh ▸ Subgroup.mem_map_of_mem π hx2⟩
    rw [hRV, Subgroup.mem_bot] at h1
    have h2 : x ∈ π.ker ⊓ Vh := ⟨h1, hx2⟩
    rwa [hVhinj] at h2
  have hRtVhP : Rt ⊔ Vh = P := by
    apply le_antisymm (sup_le hRtP hVhP)
    intro x hx
    rw [hPc] at hx
    have hx' : π x ∈ ((R ⊔ V : Subgroup S) : Set S) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R V hVR] at hx'
    obtain ⟨r, hr, v, hv, hrv⟩ := hx'
    have hv' : v ∈ Vh.map π := hVh.symm ▸ hv
    obtain ⟨w, hw, rfl⟩ := hv'
    have hxw : x * w⁻¹ ∈ Rt := by
      rw [hRt, Subgroup.mem_comap, map_mul, map_inv, ← hrv, mul_inv_cancel_right]
      exact hr
    rw [show x = x * w⁻¹ * w by group]
    exact mul_mem (Subgroup.mem_sup_left hxw) (Subgroup.mem_sup_right hw)
  have haP : a ∈ Subgroup.normalizer ((P : Subgroup E) : Set E) := by
    rw [hPc]
    exact mem_normalizer_comap π haRV
  have haRt : a ∈ Subgroup.normalizer (Rt : Set E) := mem_normalizer_comap π haRn
  refine CFSG.RankThree.PerfectCover.perfect_central_prime_kernel_abelian_radical_dilation_trivial'
    π.ker hC hCp P Rt Vh hRtP hRtab hCRt πR hπR hπRker hW hVhP hRn hRtVh hRtVhP a haP haRt
    haVh hacop ℓ hℓ fun x y hxy => ?_
  refine Subtype.ext ?_
  change π y = (π x) ^ (ℓ : ZMod p).val
  rw [hxy, map_mul, map_mul, map_inv]
  exact haR _ x.2

end Dilation

theorem splitting_of_perfect_case {E S : Type*} [Group E] [Group S] [Group.IsPerfect S]
    (π : E →* S) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hperf : ∀ D : Subgroup E, Group.IsPerfect D → Function.Surjective (π.comp D.subtype) →
      (π.comp D.subtype).ker = ⊥) :
    (∃! s : S →* E, π.comp s = MonoidHom.id S) ∧
      ∀ s : S →* E, π.comp s = MonoidHom.id S →
        ∃ e : π.ker × s.range ≃* E, ∀ c g, e (c, g) = (c : E) * g := by
  refine ⟨?_, fun s hs => LinearRoots.exists_mulEquiv_prod_of_section hC hs⟩
  obtain ⟨-, hDperf, hDs⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective π hπ hC inferInstance
  have hinj : Function.Injective (π.comp (commutator E).subtype) :=
    (MonoidHom.ker_eq_bot_iff _).1 (hperf _ hDperf hDs)
  let e := MulEquiv.ofBijective _ ⟨hinj, hDs⟩
  refine ⟨(commutator E).subtype.comp e.symm.toMonoidHom,
    MonoidHom.ext fun x => e.apply_symm_apply x, fun s hs => ?_⟩
  exact section_eq_of_forall π hC (fun δ hδ => eq_one_of_isPerfect_of_mem_center δ
    fun x => hC (hδ x)) hs (MonoidHom.ext fun x => e.apply_symm_apply x)

end CFSG.RankThree.CentralLift
