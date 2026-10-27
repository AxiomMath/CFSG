module

public import CFSG.LocalAnalysis.StandardType.GGTPWeightDefs
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.StandardType

open scoped Pointwise

private lemma ggTP_cube (a : Multiplicative (ZMod 3)) : a ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow]
  show (3 : ℕ) • a.toAdd = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private lemma ggTP_torus_cube (x : GGTPTorus) : x ^ 3 = 1 := by
  apply Subtype.ext
  funext i
  exact ggTP_cube ((x : Fin 6 → Multiplicative (ZMod 3)) i)

private lemma ggTP_isPGroup_range {P : Type} [Group P] (δ : GGTPTorus →* P) :
    IsPGroup 3 δ.range := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hy
  refine ⟨1, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, pow_one, ← map_pow, ggTP_torus_cube, map_one]
  rfl

private lemma ggTP_permAct_inv_apply (σ : Equiv.Perm (Fin 6)) (x : GGTPTorus) :
    ggTPPermAct σ (ggTPPermAct σ⁻¹ x) = x := by
  apply Subtype.ext
  funext i
  simp [ggTPPermAct]

private lemma ggTP_subtype_eq_one {G : Type} [Group G] {H : Subgroup G} (h : H) :
    (h : G) = 1 ↔ h = 1 := by
  constructor
  · intro hh; exact Subtype.ext (by simpa using hh)
  · intro hh; rw [hh]; rfl

private lemma ggTP_normalizerMonoidHom_map {G : Type} [Group G] {H : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (S : Subgroup H) :
    ((Subgroup.normalizerMonoidHom H ⟨g, hg⟩ : MulAut H) • S).map H.subtype
      = (MulAut.conj g : MulAut G) • (S.map H.subtype) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨(z : G), Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
    rw [MulAut.smul_def, MulAut.conj_apply, ← hyx, ← hzy, MulAut.smul_def]
    rfl
  · intro hx
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    rw [Subgroup.mem_map] at hw
    obtain ⟨z, hz, hzw⟩ := hw
    rw [Subgroup.mem_map]
    refine ⟨⟨g * (z : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (z : G)).mp z.2⟩, ?_, ?_⟩
    · rw [Subgroup.mem_smul_pointwise_iff_exists]
      refine ⟨z, hz, ?_⟩
      rw [MulAut.smul_def]
      rfl
    · rw [← hwx, MulAut.smul_def, MulAut.conj_apply, ← hzw]
      rfl

private lemma ggTP_conj_smul_map {G : Type} [Group G] {H : Subgroup G} (k : H) (S : Subgroup H) :
    ((MulAut.conj k : MulAut H) • S).map H.subtype
      = (MulAut.conj (k : G) : MulAut G) • (S.map H.subtype) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨(z : G), Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
    rw [MulAut.smul_def, MulAut.conj_apply, ← hyx, ← hzy, MulAut.smul_def]
    rfl
  · intro hx
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    rw [Subgroup.mem_map] at hw
    obtain ⟨z, hz, hzw⟩ := hw
    rw [Subgroup.mem_map]
    refine ⟨⟨(k : G) * (z : G) * (k : G)⁻¹, H.mul_mem (H.mul_mem k.2 z.2) (H.inv_mem k.2)⟩, ?_, ?_⟩
    · rw [Subgroup.mem_smul_pointwise_iff_exists]
      refine ⟨z, hz, ?_⟩
      rw [MulAut.smul_def]
      rfl
    · rw [← hwx, MulAut.smul_def, MulAut.conj_apply, ← hzw]
      rfl

theorem ggTPTorusLift {X P : Type} [Group X] [Finite X] [Group P] (π : X →* P)
    (hπ : Function.Surjective π) (hker : ¬ 3 ∣ Nat.card π.ker) (δ : GGTPTorus →* P)
    (hδ : ∀ x : GGTPTorus, δ x = 1 ↔ (x : Fin 6 → Multiplicative (ZMod 3)) ∈ GGTPTorusConst)
    (w : Equiv.Perm (Fin 6) → P) (hw : ∀ (σ : Equiv.Perm (Fin 6)) (x : GGTPTorus),
      w σ * δ x * (w σ)⁻¹ = δ (ggTPPermAct σ x)) :
    ∃ θ : GGTPTorus →* X, (∀ x, π (θ x) = δ x) ∧
      (∀ x : GGTPTorus, θ x = 1 ↔ (x : Fin 6 → Multiplicative (ZMod 3)) ∈ GGTPTorusConst) ∧
      ∀ σ : Equiv.Perm (Fin 6), ∃ g : X, ∀ x : GGTPTorus, g * θ x * g⁻¹ = θ (ggTPPermAct σ x) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let E : Subgroup P := δ.range
  let Pt : Subgroup X := E.comap π
  have hE3 : IsPGroup 3 E := ggTP_isPGroup_range δ
  have hker_le : π.ker ≤ Pt := by
    intro x hx
    show π x ∈ E
    rw [MonoidHom.mem_ker.mp hx]
    exact E.one_mem
  have hdom_range : (π.domRestrict Pt).range = E := by
    rw [MonoidHom.domRestrict_range, Subgroup.map_comap_eq_self_of_surjective hπ E]
  have hdom_ker : (π.domRestrict Pt).ker = π.ker.subgroupOf Pt :=
    MonoidHom.ker_domRestrict Pt π
  have hcard_dom := Subgroup.card_ker_mul_card_range (π.domRestrict Pt)
  rw [hdom_ker, hdom_range] at hcard_dom
  have hker_card : Nat.card (π.ker.subgroupOf Pt) = Nat.card π.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
  have hPtcard : Nat.card π.ker * Nat.card E = Nat.card Pt := by
    rw [← hker_card]; exact hcard_dom
  have hfac : (Nat.card Pt).factorization 3 = (Nat.card E).factorization 3 := by
    rw [← hPtcard]
    rw [Nat.factorization_mul (Nat.card_pos (α := π.ker)).ne' (Nat.card_pos (α := E)).ne']
    rw [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hker, zero_add]
  have hEcard : Nat.card E = 3 ^ (Nat.card E).factorization 3 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hE3
    rw [hn, Nat.factorization_pow_self Nat.prime_three]
  obtain ⟨S⟩ := Sylow.nonempty (p := 3) (G := Pt)
  haveI : Finite (Sylow 3 Pt) := Sylow.finite_of_finiteIndex S
  have hScard : Nat.card S = Nat.card E := by
    rw [Sylow.card_eq_multiplicity S, hfac, ← hEcard]
  let f : S →* E := (π.comp (Pt.subtype.comp (S : Subgroup Pt).subtype)).codRestrict E
    (fun s => s.1.2)
  have hf_ker : f.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro s hs
    have hpi : π ((s : S) : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hs)
    have hs_ker : ((s : S) : X) ∈ π.ker := MonoidHom.mem_ker.mpr hpi
    have hcop : Nat.Coprime (Nat.card S) (Nat.card π.ker) := by
      rw [hScard, hEcard]
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker).pow_left _
    have hdvd1 : orderOf s ∣ Nat.card S := orderOf_dvd_natCard s
    let h : π.ker := ⟨(s : X), hs_ker⟩
    have horder : orderOf s = orderOf h := by
      rw [← Subgroup.orderOf_coe s, ← Subgroup.orderOf_coe (s : Pt),
        ← Subgroup.orderOf_coe h]
    have hdvd2 : orderOf s ∣ Nat.card π.ker := by
      rw [horder]
      exact orderOf_dvd_natCard h
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)
  have hf_inj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hf_ker
  have hf_range_card : Nat.card f.range = Nat.card S := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hf_ker, Subgroup.card_bot, one_mul] at h
    exact h
  have hf_surj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [hf_range_card, hScard]
  let e : S ≃* E := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let δE : GGTPTorus →* E := δ.codRestrict E (fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  let θ : GGTPTorus →* X :=
    (Pt.subtype.comp ((S : Subgroup Pt).subtype.comp (e.symm : E →* S))).comp δE
  have hEcomm : ∀ a b : P, a ∈ E → b ∈ E → a * b = b * a := by
    intro a b ha hb
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    rw [← map_mul, ← map_mul, mul_comm]
  have hθ_pi : ∀ x, π (θ x) = δ x := by
    intro x
    show π (((e.symm (δE x) : S)) : X) = δ x
    change (f (e.symm (δE x)) : P) = δ x
    rw [show f (e.symm (δE x)) = δE x from MulEquiv.apply_symm_apply e (δE x)]
    rfl
  have hθ_one : ∀ x : GGTPTorus,
      θ x = 1 ↔ (x : Fin 6 → Multiplicative (ZMod 3)) ∈ GGTPTorusConst := by
    intro x
    have h1 : θ x = 1 ↔ e.symm (δE x) = 1 := by
      show ((e.symm (δE x) : S) : X) = 1 ↔ e.symm (δE x) = 1
      rw [ggTP_subtype_eq_one, ggTP_subtype_eq_one]
    have h2 : e.symm (δE x) = 1 ↔ δE x = 1 := MulEquiv.map_eq_one_iff (e.symm)
    have h3 : δE x = 1 ↔ δ x = 1 := (ggTP_subtype_eq_one (δE x)).symm
    exact h1.trans (h2.trans (h3.trans (hδ x)))
  refine ⟨θ, hθ_pi, hθ_one, ?_⟩
  intro σ
  obtain ⟨g₀, hg₀π⟩ := hπ (w σ)
  have hwσ_norm : w σ ∈ Subgroup.normalizer (E : Set P) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      obtain ⟨x, rfl⟩ := he
      rw [hw σ x]
      exact MonoidHom.mem_range.mpr ⟨ggTPPermAct σ x, rfl⟩
    · intro he
      obtain ⟨y, hy⟩ := he
      have hy' : δ y = w σ * δ (ggTPPermAct σ⁻¹ y) * (w σ)⁻¹ := by
        have h := hw σ (ggTPPermAct σ⁻¹ y)
        rw [ggTP_permAct_inv_apply σ y] at h
        exact h.symm
      have hfin : e = δ (ggTPPermAct σ⁻¹ y) := by
        calc e = (w σ)⁻¹ * (w σ * e * (w σ)⁻¹) * w σ := by group
          _ = (w σ)⁻¹ * δ y * w σ := by rw [hy]
          _ = (w σ)⁻¹ * (w σ * δ (ggTPPermAct σ⁻¹ y) * (w σ)⁻¹) * w σ := by rw [hy']
          _ = δ (ggTPPermAct σ⁻¹ y) := by group
      rw [hfin]
      exact MonoidHom.mem_range.mpr ⟨ggTPPermAct σ⁻¹ y, rfl⟩
  have hg₀norm : g₀ ∈ Subgroup.normalizer (Pt : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      show π (g₀ * h * g₀⁻¹) ∈ E
      have hpi : π (g₀ * h * g₀⁻¹) = w σ * π h * (w σ)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hg₀π]
      rw [hpi]
      exact (Subgroup.mem_normalizer_iff.mp hwσ_norm (π h)).mp hh
    · intro hh
      show π h ∈ E
      have hh' : w σ * π h * (w σ)⁻¹ ∈ E := by
        have hpi : π (g₀ * h * g₀⁻¹) = w σ * π h * (w σ)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hg₀π]
        rwa [← hpi]
      exact (Subgroup.mem_normalizer_iff.mp hwσ_norm (π h)).mpr hh'
  let φ : MulAut Pt := Subgroup.normalizerMonoidHom Pt ⟨g₀, hg₀norm⟩
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq Pt (φ • S) S
  let SX : Subgroup X := (S : Subgroup Pt).map Pt.subtype
  let g : X := (k : X) * g₀
  have hT : (((φ • S : Sylow 3 Pt)) : Subgroup Pt).map Pt.subtype
      = (MulAut.conj g₀ : MulAut X) • SX := by
    rw [Sylow.pointwise_smul_def]
    exact ggTP_normalizerMonoidHom_map g₀ hg₀norm (S : Subgroup Pt)
  have hk_sub : (MulAut.conj k : MulAut Pt) • (((φ • S : Sylow 3 Pt)) : Subgroup Pt)
      = (S : Subgroup Pt) := by
    rw [← Sylow.coe_subgroup_smul, hk]
  have hgS : (MulAut.conj g : MulAut X) • SX = SX := by
    have hmap := congrArg (Subgroup.map Pt.subtype) hk_sub
    rw [ggTP_conj_smul_map k (((φ • S : Sylow 3 Pt)) : Subgroup Pt)] at hmap
    rw [hT] at hmap
    rw [← mul_smul, ← MulAut.conj.map_mul] at hmap
    exact hmap
  have hinj_SX : ∀ a b : X, a ∈ SX → b ∈ SX → π a = π b → a = b := by
    intro a b ha hb hab
    change a ∈ (S : Subgroup Pt).map Pt.subtype at ha
    change b ∈ (S : Subgroup Pt).map Pt.subtype at hb
    rw [Subgroup.mem_map] at ha hb
    obtain ⟨sa, hsa, rfl⟩ := ha
    obtain ⟨sb, hsb, rfl⟩ := hb
    have hf_eq : f ⟨sa, hsa⟩ = f ⟨sb, hsb⟩ := Subtype.ext (by
      show π (sa : X) = π (sb : X)
      exact hab)
    have hst : sa = sb := congrArg Subtype.val (hf_inj hf_eq)
    rw [hst]
  have hθ_mem : ∀ y, θ y ∈ SX := by
    intro y
    change θ y ∈ (S : Subgroup Pt).map Pt.subtype
    rw [Subgroup.mem_map]
    exact ⟨(e.symm (δE y) : Pt), (e.symm (δE y)).2, rfl⟩
  refine ⟨g, ?_⟩
  intro x
  have hconj_mem : g * θ x * g⁻¹ ∈ SX := by
    have h := Subgroup.smul_mem_pointwise_smul (θ x) (MulAut.conj g) SX (hθ_mem x)
    rw [hgS] at h
    rwa [MulAut.smul_def, MulAut.conj_apply] at h
  have hπg : π g = π k * w σ := by
    show π ((k : X) * g₀) = π k * w σ
    rw [map_mul, hg₀π]
  have hpi_conj : π (g * θ x * g⁻¹) = δ (ggTPPermAct σ x) := by
    have hkE : π k ∈ E := k.2
    have hactE : δ (ggTPPermAct σ x) ∈ E :=
      MonoidHom.mem_range.mpr ⟨ggTPPermAct σ x, rfl⟩
    calc π (g * θ x * g⁻¹)
        = π k * (w σ * δ x * (w σ)⁻¹) * (π k)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hπg, hθ_pi x]
          group
      _ = π k * δ (ggTPPermAct σ x) * (π k)⁻¹ := by rw [hw σ x]
      _ = δ (ggTPPermAct σ x) := by
          rw [hEcomm (π k) (δ (ggTPPermAct σ x)) hkE hactE]
          group
  exact hinj_SX (g * θ x * g⁻¹) (θ (ggTPPermAct σ x)) hconj_mem (hθ_mem _)
    (by rw [hpi_conj, hθ_pi (ggTPPermAct σ x)])

end CFSG.StandardType

end
