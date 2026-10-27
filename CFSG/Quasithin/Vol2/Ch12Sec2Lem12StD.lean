module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12StA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative Matrix

namespace Lem12St

theorem eq_bot_of_radical {X : Type*} [Group X] [Finite X] {C K R : Subgroup X}
    (hKC : K ≤ C) (hCK : C ≤ Subgroup.normalizer (K : Set X)) (hRC : R ≤ C)
    (hCR : C ≤ Subgroup.normalizer (R : Set X)) (hR2 : IsPGroup 2 ↥R)
    (hcent : C ⊓ Subgroup.centralizer (R : Set X) ≤ R) (hK2 : pCoreOf 2 K = ⊥) : K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRK : R ⊓ K = ⊥ := by
    have hN : K ≤ Subgroup.normalizer ((R ⊓ K : Subgroup X) : Set X) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxR, hxK⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp (hCR (hKC hk)) x).mp hxR,
          K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk)⟩
      · rintro ⟨hxR, hxK⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp (hCR (hKC hk)) x).mpr hxR, ?_⟩
        have e : x = k⁻¹ * (k * x * k⁻¹) * k := by group
        rw [e]
        exact K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk
    have h := le_pCoreOf_of_le_normalizer 2 (inf_le_right : R ⊓ K ≤ K) hN
      (hR2.to_le inf_le_left)
    rw [hK2] at h
    exact eq_bot_iff.mpr h
  have hKR : K ≤ Subgroup.centralizer (R : Set X) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 : r * k * r⁻¹ * k⁻¹ ∈ R := by
      have h' : k * r⁻¹ * k⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hCR (hKC hk)) r⁻¹).mp (R.inv_mem hr)
      have e : r * k * r⁻¹ * k⁻¹ = r * (k * r⁻¹ * k⁻¹) := by group
      rw [e]
      exact R.mul_mem hr h'
    have h2 : r * k * r⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCK (hRC hr)) k).mp hk) (K.inv_mem hk)
    have h3 : r * k * r⁻¹ * k⁻¹ = 1 := by
      have h4 : r * k * r⁻¹ * k⁻¹ ∈ R ⊓ K := ⟨h1, h2⟩
      rw [hRK] at h4
      exact Subgroup.mem_bot.mp h4
    calc r * k = r * k * r⁻¹ * k⁻¹ * (k * r) := by group
      _ = k * r := by rw [h3, one_mul]
  have hKR' : K ≤ R := fun k hk => hcent ⟨hKC hk, hKR hk⟩
  have h := le_pCoreOf_of_le_normalizer 2 (le_refl K) Subgroup.le_normalizer (hR2.to_le hKR')
  rw [hK2] at h
  exact eq_bot_iff.mpr h

theorem eq_bot_of_radical_model {X Y : Type*} [Group X] [Finite X] [Group Y] {C K : Subgroup X}
    (ι : Y →* X) (hι : Function.Injective ι) (hCι : C ≤ ι.range) (R' : Subgroup Y)
    (hKC : K ≤ C) (hCK : C ≤ Subgroup.normalizer (K : Set X)) (hRC : ∀ r ∈ R', ι r ∈ C)
    (hCR : ∀ y, ι y ∈ C → ∀ r ∈ R', y * r * y⁻¹ ∈ R') (hR2 : ∀ r ∈ R', r ^ 2 = 1)
    (hcent : ∀ y, ι y ∈ C → (∀ r ∈ R', r * y = y * r) → y ∈ R') (hK2 : pCoreOf 2 K = ⊥) :
    K = ⊥ := by
  refine eq_bot_of_radical (R := R'.map ι) hKC hCK ?_ ?_ ?_ ?_ hK2
  · rintro _ ⟨r, hr, rfl⟩
    exact hRC r hr
  · intro c hc
    obtain ⟨y, rfl⟩ := hCι hc
    have hyi : ι y⁻¹ ∈ C := by rw [map_inv]; exact C.inv_mem hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨y * r * y⁻¹, hCR y hc r hr, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨r, hr, hrx⟩
      refine ⟨y⁻¹ * r * y⁻¹⁻¹, hCR y⁻¹ hyi r hr, ?_⟩
      rw [map_mul, map_mul, map_inv, inv_inv, hrx]
      group
  · rintro ⟨_, r, hr, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, SubgroupClass.coe_pow, ← map_pow, hR2 r hr, map_one, OneMemClass.coe_one]
  · rintro c ⟨hc, hcR⟩
    obtain ⟨y, rfl⟩ := hCι hc
    refine ⟨y, hcent y hc fun r hr => hι ?_, rfl⟩
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.mp hcR) (ι r) ⟨r, hr, rfl⟩

section Radical

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def IsRadU (U : Submodule F (Fin n → F)) (g : Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ x, g *ᵥ x - x ∈ U) ∧ ∀ u ∈ U, g *ᵥ u = u

variable {U : Submodule F (Fin n → F)}

theorem isRadU_one : IsRadU U 1 :=
  ⟨fun x => by simp, fun u _ => by simp⟩

theorem isRadU_mul {g h : Matrix (Fin n) (Fin n) F} (hg : IsRadU U g) (hh : IsRadU U h) :
    IsRadU U (g * h) := by
  refine ⟨fun x => ?_, fun u hu => ?_⟩
  · rw [← Matrix.mulVec_mulVec]
    have e : g *ᵥ (h *ᵥ x) - x = (g *ᵥ (h *ᵥ x) - h *ᵥ x) + (h *ᵥ x - x) := by abel
    rw [e]
    exact U.add_mem (hg.1 _) (hh.1 x)
  · rw [← Matrix.mulVec_mulVec, hh.2 u hu, hg.2 u hu]

theorem isRadU_of_mul_eq_one {g h : Matrix (Fin n) (Fin n) F} (hg : IsRadU U g)
    (hgh : g * h = 1) (hhg : h * g = 1) : IsRadU U h := by
  have hgi : ∀ x, g *ᵥ (h *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hgh, Matrix.one_mulVec]
  refine ⟨fun x => ?_, fun u hu => ?_⟩
  · have h1 := hg.1 (h *ᵥ x)
    rw [hgi] at h1
    have e : h *ᵥ x - x = -(x - h *ᵥ x) := by abel
    rw [e]
    exact U.neg_mem h1
  · conv_lhs => rw [← hg.2 u hu]
    rw [Matrix.mulVec_mulVec, hhg, Matrix.one_mulVec]

theorem mul_self_of_isRadU (h2 : (2 : F) = 0) {g : Matrix (Fin n) (Fin n) F} (hg : IsRadU U g) :
    g * g = 1 := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  set x : Fin n → F := Pi.single i 1
  set y := g *ᵥ x - x with hy
  have hgx : g *ᵥ x = x + y := by rw [hy]; abel
  have hyy : y + y = 0 := by rw [← two_smul F y, h2, zero_smul]
  rw [hgx, Matrix.mulVec_add, hgx, hg.2 y (hg.1 x), add_assoc, hyy, add_zero]

theorem isRadU_conj {c c' g : Matrix (Fin n) (Fin n) F} (hcU : ∀ u ∈ U, c *ᵥ u ∈ U)
    (hc'U : ∀ u ∈ U, c' *ᵥ u ∈ U) (hcc : c * c' = 1) (hg : IsRadU U g) :
    IsRadU U (c * g * c') := by
  refine ⟨fun x => ?_, fun u hu => ?_⟩
  · have e : (c * g * c') *ᵥ x - x = c *ᵥ (g *ᵥ (c' *ᵥ x) - c' *ᵥ x) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        hcc, Matrix.one_mulVec]
    rw [e]
    exact hcU _ (hg.1 _)
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg.2 _ (hc'U u hu), Matrix.mulVec_mulVec,
      hcc, Matrix.one_mulVec]

theorem transv_mulVec (u φ x : Fin n → F) :
    (1 + Matrix.vecMulVec u φ) *ᵥ x = x + (φ ⬝ᵥ x) • u := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]

theorem det_transv {u φ : Fin n → F} (h : φ ⬝ᵥ u = 0) : (1 + Matrix.vecMulVec u φ).det = 1 := by
  rw [Matrix.vecMulVec_eq (ι := Unit), Matrix.det_one_add_replicateCol_mul_replicateRow, h,
    add_zero]

theorem isRadU_transv {u φ : Fin n → F} (hu : u ∈ U) (hφ : ∀ u' ∈ U, φ ⬝ᵥ u' = 0) :
    IsRadU U (1 + Matrix.vecMulVec u φ) := by
  refine ⟨fun x => ?_, fun u' hu' => ?_⟩
  · rw [transv_mulVec, add_sub_cancel_left]
    exact U.smul_mem _ hu
  · rw [transv_mulVec, hφ u' hu', zero_smul, add_zero]

theorem exists_form_of_not_mem {y : Fin n → F} (hy : y ∉ U) :
    ∃ φ : Fin n → F, (∀ u ∈ U, φ ⬝ᵥ u = 0) ∧ φ ⬝ᵥ y = 1 := by
  have hq : U.mkQ y ≠ 0 := by
    rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
    exact hy
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual F ((Fin n → F) ⧸ U), ψ (U.mkQ y) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hq ((Module.forall_dual_apply_eq_zero_iff F _).mp hcon)
  set φ' : Module.Dual F (Fin n → F) := ψ ∘ₗ U.mkQ with hφ'
  set w : Fin n → F := fun i => φ' fun j => if i = j then 1 else 0 with hw
  have hφw : ∀ x, φ' x = w ⬝ᵥ x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ φ' x, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  have hφy : φ' y ≠ 0 := hψ
  refine ⟨(φ' y)⁻¹ • w, fun u hu => ?_, ?_⟩
  · have hu0 : φ' u = 0 := by
      rw [hφ', LinearMap.comp_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero U).mpr hu, map_zero]
    rw [smul_dotProduct, ← hφw, hu0, smul_zero]
  · rw [smul_dotProduct, ← hφw, smul_eq_mul, inv_mul_cancel₀ hφy]

theorem isRadU_of_commute (hF : ∀ a : F, a = 0 ∨ a = 1) {u₀ y₀ : Fin n → F} (hu₀ : u₀ ∈ U)
    (hu₀1 : u₀ ≠ 0) (hy₀ : y₀ ∉ U) {c : Matrix (Fin n) (Fin n) F}
    (hc : ∀ x, c *ᵥ x = 0 → x = 0)
    (hcomm : ∀ u ∈ U, ∀ φ : Fin n → F, (∀ u' ∈ U, φ ⬝ᵥ u' = 0) →
      c * (1 + Matrix.vecMulVec u φ) = (1 + Matrix.vecMulVec u φ) * c) :
    IsRadU U c := by
  have hkey : ∀ u ∈ U, ∀ φ : Fin n → F, (∀ u' ∈ U, φ ⬝ᵥ u' = 0) → ∀ x,
      (φ ⬝ᵥ x) • (c *ᵥ u) = (φ ⬝ᵥ (c *ᵥ x)) • u := by
    intro u hu φ hφ x
    have h := congrArg (fun M => M *ᵥ x) (hcomm u hu φ hφ)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, transv_mulVec, transv_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_smul] at h
    exact add_left_cancel h
  obtain ⟨φ₀, hφ₀U, hφ₀y⟩ := exists_form_of_not_mem hy₀
  have hcU : ∀ u ∈ U, c *ᵥ u = u := by
    intro u hu
    have h := hkey u hu φ₀ hφ₀U y₀
    rw [hφ₀y, one_smul] at h
    rcases hF (φ₀ ⬝ᵥ (c *ᵥ y₀)) with h0 | h1
    · rw [h0, zero_smul] at h
      rw [h]
      exact (hc u h).symm
    · rw [h1, one_smul] at h
      exact h
  refine ⟨fun x => ?_, hcU⟩
  by_contra hx
  obtain ⟨φ, hφU, hφx⟩ := exists_form_of_not_mem hx
  have h := hkey u₀ hu₀ φ hφU x
  rw [hcU u₀ hu₀, ← sub_eq_zero, ← sub_smul, smul_eq_zero] at h
  rcases h with h | h
  · rw [dotProduct_sub, ← sub_eq_zero.mp h, sub_self] at hφx
    exact zero_ne_one hφx
  · exact hu₀1 h

@[expose] def radSub {Y : Type*} [Group Y] (mat : Y →* Matrix (Fin n) (Fin n) F)
    (U : Submodule F (Fin n → F)) : Subgroup Y where
  carrier := {y | IsRadU U (mat y)}
  mul_mem' {a b} ha hb := by
    change IsRadU U (mat (a * b))
    rw [map_mul]
    exact isRadU_mul ha hb
  one_mem' := by
    change IsRadU U (mat 1)
    rw [map_one]
    exact isRadU_one
  inv_mem' {a} ha := by
    change IsRadU U (mat a⁻¹)
    refine isRadU_of_mul_eq_one ha ?_ ?_
    · rw [← map_mul, mul_inv_cancel, map_one]
    · rw [← map_mul, inv_mul_cancel, map_one]

variable {Y : Type*} [Group Y] {mat : Y →* Matrix (Fin n) (Fin n) F}

theorem mem_radSub_iff {y : Y} : y ∈ radSub mat U ↔ IsRadU U (mat y) :=
  Iff.rfl

theorem sq_eq_one_of_mem_radSub (h2 : (2 : F) = 0) (hmat : Function.Injective mat) {r : Y}
    (hr : r ∈ radSub mat U) : r ^ 2 = 1 := by
  apply hmat
  rw [map_pow, pow_two, map_one]
  exact mul_self_of_isRadU h2 hr

theorem conj_mem_radSub {y r : Y} (hyU : ∀ u ∈ U, mat y *ᵥ u ∈ U)
    (hyiU : ∀ u ∈ U, mat y⁻¹ *ᵥ u ∈ U) (hr : r ∈ radSub mat U) : y * r * y⁻¹ ∈ radSub mat U := by
  rw [mem_radSub_iff, map_mul, map_mul]
  refine isRadU_conj hyU hyiU ?_ hr
  rw [← map_mul, mul_inv_cancel, map_one]

theorem mem_radSub_of_commute (hF : ∀ a : F, a = 0 ∨ a = 1) {u₀ y₀ : Fin n → F} (hu₀ : u₀ ∈ U)
    (hu₀1 : u₀ ≠ 0) (hy₀ : y₀ ∉ U)
    (htr : ∀ u ∈ U, ∀ φ : Fin n → F, (∀ u' ∈ U, φ ⬝ᵥ u' = 0) →
      ∃ t : Y, mat t = 1 + Matrix.vecMulVec u φ)
    {y : Y} (hy : ∀ r ∈ radSub mat U, r * y = y * r) : y ∈ radSub mat U := by
  refine isRadU_of_commute hF hu₀ hu₀1 hy₀ (fun x hx => ?_) fun u hu φ hφ => ?_
  · have h := congrArg (fun w => mat y⁻¹ *ᵥ w) hx
    simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec,
      Matrix.mulVec_zero] at h
    exact h
  · obtain ⟨t, ht⟩ := htr u hu φ hφ
    have htR : t ∈ radSub mat U := by
      rw [mem_radSub_iff, ht]
      exact isRadU_transv hu hφ
    rw [← ht, ← map_mul, ← map_mul, hy t htR]

end Radical

section Stab

variable {G : Type} [Group G] {L V : Subgroup G}

theorem stab_le_autOn (hLV : L ≤ Subgroup.normalizer (V : Set G)) {v : G} (hv : v ∈ V) :
    autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) (⟨v, hv⟩ : ↥V) ≤
      autOn (L ⊓ Subgroup.centralizer ({v} : Set G)) V := by
  have hNV : L ⊓ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans hLV
  rintro a ⟨ha, hav⟩
  obtain ⟨⟨l, hl⟩, rfl⟩ := (A4.mem_autOn_iff hLV).mp ha
  have h1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hav)
  change ((A4.actionOn V L hLV ⟨l, hl⟩ ⟨v, hv⟩ : ↥V) : G) = v at h1
  rw [A4.actionOn_apply_coe] at h1
  have hlv : l ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc l * v = l * v * l⁻¹ * l := by group
      _ = v * l := by rw [h1]
  refine (A4.mem_autOn_iff hNV).mpr ⟨⟨l, hl, hlv⟩, ?_⟩
  refine MulEquiv.ext fun w => Subtype.ext ?_
  rw [A4.actionOn_apply_coe, A4.actionOn_apply_coe]

theorem stab_le_normalizer (hLV : L ≤ Subgroup.normalizer (V : Set G)) {v : G} (hv : v ∈ V) :
    autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) (⟨v, hv⟩ : ↥V) ≤
      Subgroup.normalizer
        (autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V : Set (MulAut ↥V)) := by
  have hNV : L ⊓ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans hLV
  exact (stab_le_autOn hLV hv).trans
    (autOn_le_normalizer_autOn ((oTwoUpper_le _).trans hNV) hNV (le_normalizer_oTwoUpper _))

end Stab

section Natural

theorem eq_zero_or_eq_one_of_card_two {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2)
    (a : F) : a = 0 ∨ a = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rcases eq_or_ne a 0 with h0 | h0
  · exact Or.inl h0
  · right
    have h := FiniteField.pow_card_sub_one_eq_one a h0
    rwa [← Nat.card_eq_fintype_card, hF, show 2 - 1 = 1 from rfl, pow_one] at h

theorem two_eq_zero_of_forall {F : Type*} [Field F] (hF : ∀ a : F, a = 0 ∨ a = 1) :
    (2 : F) = 0 := by
  rcases hF 2 with h | h
  · exact h
  · exfalso
    have h1 : (1 : F) = 0 := by
      calc (1 : F) = (1 + 1) - 1 := by ring
        _ = 0 := by rw [one_add_one_eq_two, h, sub_self]
    exact one_ne_zero h1

theorem exists_natEquivTop {W : Type*} [CommGroup W] {n : ℕ} {F : Type} [Field F]
    {H : Subgroup (MulAut W)} {π : ↥(StatedSL n F) →* ↥H}
    (hR : (FFModel.nat (StatedSL n F)).RealizesVia H ⊤ ⊥ π) :
    ∃ e : W ≃* Multiplicative (Fin n → F), ∀ (g : ↥(StatedSL n F)) (x : W),
      e (((π g : ↥H) : MulAut W) x) = natAct (StatedSL n F) g (e x) := by
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.RealizesVia.secMap rfl hR
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 := (hfk u).1 hu
    rw [Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  let e : W ≃* Multiplicative (Fin n → F) :=
    (Subgroup.topEquiv (G := W)).symm.trans ((MulEquiv.ofBijective f ⟨hinj, hfs⟩).trans
      (Subgroup.topEquiv (G := Multiplicative (Fin n → F))))
  exact ⟨e, fun g x => hfe g ⟨x, Subgroup.mem_top x⟩ (Subgroup.mem_top _)⟩

variable {G : Type} [Group G] [Finite G] {L V : Subgroup G} [IsMulCommutative ↥V]

theorem false_of_natural (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ} (hn : 2 ≤ n)
    (hbn : BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ n 1) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hK2 : pCoreOf 2 (autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V) = ⊥)
    (hVL : V = ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))⁆) : False := by
  classical
  obtain ⟨F, _, _, hF2, π, hπ⟩ := hbn
  have hF : ∀ a : F, a = 0 ∨ a = 1 := eq_zero_or_eq_one_of_card_two (by rw [hF2, pow_one])
  have h2F : (2 : F) = 0 := two_eq_zero_of_forall hF
  obtain ⟨e, he⟩ := exists_natEquivTop hπ
  set b : ↥V → (Fin n → F) := fun x => Multiplicative.toAdd (e x) with hb
  have hbe : ∀ (γ : ↥(StatedSL n F)) (x : ↥V), b (((π γ : ↥(autOn L V)) : MulAut ↥V) x) =
      ((γ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ b x := by
    intro γ x
    exact congrArg Multiplicative.toAdd (he γ x)
  have hbinj : Function.Injective b := fun x y h =>
    e.injective (Multiplicative.toAdd.injective h)
  have hbsurj : Function.Surjective b := fun y => by
    obtain ⟨x, hx⟩ := e.surjective (Multiplicative.ofAdd y)
    exact ⟨x, by rw [hb]; simp only [hx, toAdd_ofAdd]⟩
  have hπi : Function.Injective π := by
    intro γ₁ γ₂ h12
    apply Subtype.ext
    apply Units.ext
    refine Matrix.ext_of_mulVec_single fun i => ?_
    obtain ⟨x, hx⟩ := hbsurj (Pi.single i 1)
    have h1 := hbe γ₁ x
    rw [h12, hbe γ₂ x, hx] at h1
    exact h1.symm
  set e₀ := b ⟨v, hv⟩ with he₀
  have he₀1 : e₀ ≠ 0 := by
    intro h
    apply hv1
    have h1 : b ⟨v, hv⟩ = b 1 := by
      rw [← he₀, h, hb]
      simp
    exact congrArg Subtype.val (hbinj h1)
  set C := autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) (⟨v, hv⟩ : ↥V) with hC
  set K := autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V with hK
  let ι : ↥(StatedSL n F) →* MulAut ↥V := (autOn L V).subtype.comp π
  have hιi : Function.Injective ι := Subtype.val_injective.comp hπi
  let mat : ↥(StatedSL n F) →* Matrix (Fin n) (Fin n) F :=
    (Units.coeHom (Matrix (Fin n) (Fin n) F)).comp (StatedSL n F).subtype
  have hmat : Function.Injective mat := fun x y h => Subtype.ext (Units.ext h)
  have hCι : C ≤ ι.range := by
    rintro c ⟨hc, -⟩
    obtain ⟨γ, hγ⟩ := hπ.1 ⟨c, hc⟩
    exact ⟨γ, congrArg Subtype.val hγ⟩
  have hCe : ∀ y, ι y ∈ C ↔ mat y *ᵥ e₀ = e₀ := by
    intro y
    have hfix : ι y ∈ MulAction.stabilizer (MulAut ↥V) (⟨v, hv⟩ : ↥V) ↔
        ((π y : ↥(autOn L V)) : MulAut ↥V) ⟨v, hv⟩ = ⟨v, hv⟩ := MulAction.mem_stabilizer_iff
    constructor
    · rintro ⟨-, hy⟩
      have h1 := congrArg b (hfix.mp hy)
      rw [hbe] at h1
      exact h1
    · intro hy
      refine ⟨(π y).2, hfix.mpr (hbinj ?_)⟩
      rw [hbe]
      exact hy
  set U : Submodule F (Fin n → F) := Submodule.span F {e₀} with hU
  have he₀U : e₀ ∈ U := Submodule.mem_span_singleton_self e₀
  have hstabU : ∀ y, mat y *ᵥ e₀ = e₀ → ∀ u ∈ U, mat y *ᵥ u ∈ U := by
    intro y hy u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [Matrix.mulVec_smul, hy]
    exact U.smul_mem a he₀U
  have hinvfix : ∀ y, mat y *ᵥ e₀ = e₀ → mat y⁻¹ *ᵥ e₀ = e₀ := by
    intro y hy
    conv_lhs => rw [← hy]
    rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
  have hUtop : U ≠ ⊤ := by
    intro h
    have h1 := finrank_span_singleton (K := F) he₀1
    rw [← hU, h, finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ ∉ U := by
    by_contra hcon
    push Not at hcon
    exact hUtop (eq_top_iff.mpr fun y _ => hcon y)
  have htr : ∀ u ∈ U, ∀ φ : Fin n → F, (∀ u' ∈ U, φ ⬝ᵥ u' = 0) →
      ∃ t : ↥(StatedSL n F), mat t = 1 + Matrix.vecMulVec u φ := by
    intro u hu φ hφ
    have hdet := det_transv (hφ u hu)
    refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + Matrix.vecMulVec u φ)
      (by rw [hdet]; exact one_ne_zero), Subgroup.subset_closure ?_⟩, rfl⟩
    exact hdet
  refine autOn_ne_bot (((oTwoUpper_le _).trans inf_le_left).trans hLV) hVL hv hv1
    (eq_bot_of_radical_model ι hιi hCι (radSub mat U) (autOn_le_stab hLV hv)
      (stab_le_normalizer hLV hv) (fun r hr => (hCe r).mpr (hr.2 e₀ he₀U)) ?_
      (fun r hr => sq_eq_one_of_mem_radSub h2F hmat hr) ?_ hK2)
  · intro y hy r hr
    have hy' := (hCe y).mp hy
    exact conj_mem_radSub (hstabU y hy') (hstabU y⁻¹ (hinvfix y hy')) hr
  · intro y _ hy
    exact mem_radSub_of_commute hF he₀U he₀1 hy₀ htr hy

end Natural

end Lem12St

end CFSG.Quasithin.H13
