module

public import CFSG.RankThree.GF2n.Smith81.Lin31Two
public import CFSG.RankThree.GF2n.Smith81.LinRestModel
public import CFSG.RankThree.GF2n.Smith81.LinRestAlg
public import CFSG.RankThree.GF2n.Smith81.LinRestLx

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

namespace RestModel

variable {M Q Z : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} (R : RestModel M Q Z n V₁ V₂)

@[expose] def symm : RestModel M Q Z n V₂ V₁ where
  hyp := R.hyp
  ZV₁ := R.ZV₂
  V₁Q := R.V₂Q
  ZV₂ := R.ZV₁
  V₂Q := R.V₁Q
  V₁₂ := by rw [inf_comm]; exact R.V₁₂
  dec := by
    have hn : ∀ a ∈ V₁, ∀ q ∈ Q, q * a * q⁻¹ ∈ V₁ := fun a ha q hq =>
      (Subgroup.mem_normalizer_iff.mp (Q_le_normalizer_of_Z_le R.hyp R.ZV₁ R.V₁Q hq) a).mp ha
    exact decomp_swap hn R.V₂Q R.dec
  K := R.K
  γ := R.γ
  M₀ := R.M₀
  gm := R.gm
  φ := R.φ
  φπ := R.φπ
  φker := R.φker
  φQf := R.φQf
  W₁ := R.W₂
  W₂ := R.W₁
  memW₁ := R.memW₂
  memW₂ := R.memW₁
  hsup := by rw [sup_comm]; exact R.hsup
  hint := by rw [inf_comm]; exact R.hint
  iso₁ := R.iso₂
  iso₂ := R.iso₁
  card_W₁ := R.card_W₂
  card_W₂ := R.card_W₁

theorem B_inv (m : ↥(H0 M Z)) (e f : R.M₀.E) :
    R.M₀.B (R.φ m e) (R.φ m f) = R.M₀.B e f := by
  have e1 : R.φ m (e + f) = R.φ m e + R.φ m f := map_add (R.φ m) e f
  have h1 := R.M₀.Qf_add (R.φ m e) (R.φ m f)
  rw [← e1, R.φQf, R.φQf, R.φQf] at h1
  linear_combination (R.M₀.Qf_add e f) - h1

theorem φ_mem_W₁ (m : ↥(H0 M Z)) (hm : (m : G) ∈ Subgroup.normalizer (V₁ : Set G))
    {e : R.M₀.E} (he : e ∈ R.W₁) : R.φ m e ∈ R.W₁ := by
  obtain ⟨v, hv, hvQ, rfl⟩ := (R.memW₁ e).mp he
  have hcv : (m : G) * v * (m : G)⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp hm v).mp hv
  rw [← R.φπ m v hvQ]
  exact (R.memW₁ _).mpr (R.M₀.pi_mem_img hcv (R.V₁Q hcv))

theorem φ_mem_W₂ (m : ↥(H0 M Z)) (hm : (m : G) ∈ Subgroup.normalizer (V₂ : Set G))
    {e : R.M₀.E} (he : e ∈ R.W₂) : R.φ m e ∈ R.W₂ :=
  R.symm.φ_mem_W₁ m hm he

theorem φ_sq (m : ↥(H0 M Z)) (hm : (m : G) * (m : G) = 1) (e : R.M₀.E) :
    R.φ m (R.φ m e) = e := by
  have h : R.φ (m * m) = 1 :=
    (R.φker _).mpr (by rw [Subgroup.coe_mul, hm]; exact Q.one_mem)
  have := LinearEquiv.congr_fun h e
  rwa [map_mul, LinearEquiv.mul_apply] at this

@[expose] def xact (x : G) (hx : x ∈ H0 M Z) : XAct R.M₀ x where
  T := R.φ ⟨x, hx⟩
  hπ := fun y hy => R.φπ ⟨x, hx⟩ y hy
  hQ := R.φQf ⟨x, hx⟩
  hB := R.B_inv ⟨x, hx⟩

@[expose] def Nsp {x : G} (hx : x ∈ H0 M Z) : Submodule R.K R.M₀.E :=
  LinearMap.range ((R.φ ⟨x, hx⟩ : R.M₀.E →ₗ[R.K] R.M₀.E) - LinearMap.id)

theorem mem_Nsp {x : G} (hx : x ∈ H0 M Z) (e : R.M₀.E) :
    e ∈ R.Nsp hx ↔ ∃ u, R.φ ⟨x, hx⟩ u - u = e := by
  simp [Nsp, LinearMap.mem_range]

theorem mem_comm_sup_iff {x : G} (hx : x ∈ H0 M Z) (hx2 : x * x = 1) {y : G} :
    y ∈ (⁅Q, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) ↔ y ∈ Q ∧ R.M₀.π y ∈ R.Nsp hx := by
  have hxM : x ∈ M := hx.1
  have hZQ := R.hyp.Z_normal.1
  have hW : (⁅Q, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) = preimageSub R.M₀ (R.Nsp hx) := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rw [commutator_zpowers_eq_closure hx2, Subgroup.closure_le]
        rintro _ ⟨q, hq, rfl⟩
        rw [SetLike.mem_coe, mem_preimageSub]
        refine ⟨comm_mem_Q R.hyp hxM hq, ?_⟩
        rw [(R.xact x hx).pi_comm R.hyp hxM hq]
        refine (R.mem_Nsp hx _).mpr ⟨-(R.M₀.π q), ?_⟩
        simp [xact, sub_eq_add_neg, add_comm]
      · intro z hz
        rw [mem_preimageSub]
        exact ⟨hZQ hz, by rw [(R.M₀.π_ker z (hZQ hz)).mpr hz]; exact Submodule.zero_mem _⟩
    · intro y hy
      rw [mem_preimageSub] at hy
      obtain ⟨hyQ, hy⟩ := hy
      obtain ⟨u, hu⟩ := (R.mem_Nsp hx _).mp hy
      obtain ⟨q, hq, hπq⟩ := R.M₀.π_surj (-u)
      have h1 : R.M₀.π ⁅q, x⁆ = R.M₀.π y := by
        rw [(R.xact x hx).pi_comm R.hyp hxM hq, hπq, ← hu]
        simp [xact, sub_eq_add_neg, add_comm]
      have h2 : y⁻¹ * ⁅q, x⁆ ∈ Z := by
        refine (R.M₀.π_ker _ (Q.mul_mem (Q.inv_mem hyQ) (comm_mem_Q R.hyp hxM hq))).mp ?_
        rw [R.M₀.π_mul _ (Q.inv_mem hyQ) _ (comm_mem_Q R.hyp hxM hq),
          Tim79.QuadModel.pi_inv R.M₀ hyQ, h1]
        exact neg_add_cancel _
      have h3 : y = ⁅q, x⁆ * (y⁻¹ * ⁅q, x⁆)⁻¹ := by group
      rw [h3]
      exact Subgroup.mul_mem_sup
        (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers x)) (Z.inv_mem h2)
  rw [hW, mem_preimageSub]

theorem comm_sup_eq_preimage {x : G} (hx : x ∈ H0 M Z) (hx2 : x * x = 1)
    (hxn₁ : x ∈ Subgroup.normalizer (V₁ : Set G))
    (hxn₂ : x ∈ Subgroup.normalizer (V₂ : Set G)) :
    (⁅V₁, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) =
      preimageSub R.M₀ (R.Nsp hx ⊓ R.W₁) := by
  ext y
  rw [mem_preimageSub]
  have hZQ := R.hyp.Z_normal.1
  constructor
  · intro hy
    have hyQQ : y ∈ (⁅Q, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) :=
      (sup_le_sup_right (Subgroup.commutator_mono R.V₁Q le_rfl) Z) hy
    have h1 := (R.mem_comm_sup_iff hx hx2).mp hyQQ
    have hyV : y ∈ V₁ := (sup_le (commutator_zpowers_le hxn₁) R.ZV₁) hy
    exact ⟨h1.1, h1.2, (R.memW₁ _).mpr (R.M₀.pi_mem_img hyV h1.1)⟩
  · rintro ⟨hyQ, hyc, hyW⟩
    have hyQQ := (R.mem_comm_sup_iff hx hx2).mpr ⟨hyQ, hyc⟩
    have hyV : y ∈ V₁ := (R.M₀.mem_img_iff R.ZV₁ hyQ).mp ((R.memW₁ _).mp hyW)
    exact comm_Q_inf_V R.hyp R.ZV₁ R.V₁Q R.ZV₂ R.V₂Q R.V₁₂ R.dec hx2 hxn₁ hxn₂ hyQQ hyV

theorem card_comm_sup_V₁ {x : G} (hx : x ∈ H0 M Z) (hx2 : x * x = 1)
    (hxn₁ : x ∈ Subgroup.normalizer (V₁ : Set G))
    (hxn₂ : x ∈ Subgroup.normalizer (V₂ : Set G)) :
    Nat.card ↥(⁅V₁, Subgroup.zpowers x⁆ ⊔ Z) =
      Nat.card ↥(R.Nsp hx ⊓ R.W₁) * Nat.card Z := by
  rw [R.comm_sup_eq_preimage hx hx2 hxn₁ hxn₂]
  exact card_preimageSub (M₀ := R.M₀) R.hyp.Z_normal.1 _

theorem card_comm_sup_V₂ {x : G} (hx : x ∈ H0 M Z) (hx2 : x * x = 1)
    (hxn₁ : x ∈ Subgroup.normalizer (V₁ : Set G))
    (hxn₂ : x ∈ Subgroup.normalizer (V₂ : Set G)) :
    Nat.card ↥(⁅V₂, Subgroup.zpowers x⁆ ⊔ Z) =
      Nat.card ↥(R.Nsp hx ⊓ R.W₂) * Nat.card Z :=
  R.symm.card_comm_sup_V₁ hx hx2 hxn₂ hxn₁

theorem exists_pre_W₁ {x : G} (hx : x ∈ H0 M Z) (hxn₁ : x ∈ Subgroup.normalizer (V₁ : Set G))
    (hxn₂ : x ∈ Subgroup.normalizer (V₂ : Set G)) {e : R.M₀.E}
    (he : e ∈ R.Nsp hx) (heW : e ∈ R.W₁) :
    ∃ u ∈ R.W₁, R.φ ⟨x, hx⟩ u - u = e := by
  obtain ⟨w, hw⟩ := (R.mem_Nsp hx e).mp he
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp
    (show w ∈ R.W₁ ⊔ R.W₂ by rw [R.hsup]; exact Submodule.mem_top)
  have h1 : R.φ ⟨x, hx⟩ w₁ - w₁ ∈ R.W₁ :=
    R.W₁.sub_mem (R.φ_mem_W₁ ⟨x, hx⟩ hxn₁ hw₁) hw₁
  have h2 : R.φ ⟨x, hx⟩ w₂ - w₂ ∈ R.W₂ :=
    R.W₂.sub_mem (R.φ_mem_W₂ ⟨x, hx⟩ hxn₂ hw₂) hw₂
  have hsplit : R.φ ⟨x, hx⟩ (w₁ + w₂) - (w₁ + w₂) =
      (R.φ ⟨x, hx⟩ w₁ - w₁) + (R.φ ⟨x, hx⟩ w₂ - w₂) := by
    rw [map_add]; abel
  rw [hsplit] at hw
  have h3 : R.φ ⟨x, hx⟩ w₂ - w₂ ∈ R.W₁ ⊓ R.W₂ := by
    refine ⟨?_, h2⟩
    have : R.φ ⟨x, hx⟩ w₂ - w₂ = e - (R.φ ⟨x, hx⟩ w₁ - w₁) := by rw [← hw]; abel
    rw [this]
    exact R.W₁.sub_mem heW h1
  rw [R.hint, Submodule.mem_bot] at h3
  refine ⟨w₁, hw₁, ?_⟩
  rw [← hw, h3, add_zero]

theorem exists_pre_W₂ {x : G} (hx : x ∈ H0 M Z) (hxn₁ : x ∈ Subgroup.normalizer (V₁ : Set G))
    (hxn₂ : x ∈ Subgroup.normalizer (V₂ : Set G)) {e : R.M₀.E}
    (he : e ∈ R.Nsp hx) (heW : e ∈ R.W₂) :
    ∃ u ∈ R.W₂, R.φ ⟨x, hx⟩ u - u = e :=
  R.symm.exists_pre_W₁ hx hxn₂ hxn₁ he heW

theorem exists_decomp_Nsp {x : G} (hx : x ∈ H0 M Z)
    (hxn₁ : x ∈ Subgroup.normalizer (V₁ : Set G))
    (hxn₂ : x ∈ Subgroup.normalizer (V₂ : Set G)) {e : R.M₀.E}
    (he : e ∈ R.Nsp hx) :
    ∃ e₁ ∈ R.Nsp hx ⊓ R.W₁, ∃ e₂ ∈ R.Nsp hx ⊓ R.W₂, e = e₁ + e₂ := by
  obtain ⟨w, hw⟩ := (R.mem_Nsp hx e).mp he
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp
    (show w ∈ R.W₁ ⊔ R.W₂ by rw [R.hsup]; exact Submodule.mem_top)
  have h1 : R.φ ⟨x, hx⟩ w₁ - w₁ ∈ R.W₁ :=
    R.W₁.sub_mem (R.φ_mem_W₁ ⟨x, hx⟩ hxn₁ hw₁) hw₁
  have h2 : R.φ ⟨x, hx⟩ w₂ - w₂ ∈ R.W₂ :=
    R.W₂.sub_mem (R.φ_mem_W₂ ⟨x, hx⟩ hxn₂ hw₂) hw₂
  refine ⟨R.φ ⟨x, hx⟩ w₁ - w₁, ⟨(R.mem_Nsp hx _).mpr ⟨w₁, rfl⟩, h1⟩,
    R.φ ⟨x, hx⟩ w₂ - w₂, ⟨(R.mem_Nsp hx _).mpr ⟨w₂, rfl⟩, h2⟩, ?_⟩
  rw [← hw, map_add]; abel

end RestModel

theorem exists_eq_smul_of_card {K E : Type} [Field K] [Finite K] [AddCommGroup E] [Module K E]
    {P : Submodule K E} (hP : Nat.card ↥P = Nat.card K) {b : E} (hb : b ∈ P) (hb0 : b ≠ 0)
    {u : E} (hu : u ∈ P) : ∃ s : K, u = s • b := by
  have hfin : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hP]; exact Nat.card_pos.ne')
  have hinj : Function.Injective (fun s : K => (⟨s • b, P.smul_mem s hb⟩ : ↥P)) := by
    intro s t hst
    have : s • b = t • b := congrArg Subtype.val hst
    exact smul_left_injective K hb0 this
  have hsurj := (Function.Injective.bijective_of_nat_card_le hinj (by rw [hP])).2
  obtain ⟨s, hs⟩ := hsurj ⟨u, hu⟩
  exact ⟨s, (congrArg Subtype.val hs).symm⟩

section Sit

variable {M Q Z B X : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} {x : G}

theorem c4_of_A (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn3 : 3 ≤ n) (hs : Sit M Q Z X x) {A : Subgroup G}
    (hA : IsZConjugate Z A) (hAQ : A ≤ Q) (hAX : A ≤ QB X) :
    ∀ z' ∈ Z, InZClass Z (x * z') → z' = 1 := by
  intro z' hz' hcl
  by_contra hz1
  have H := hc.hyp
  obtain ⟨V₁', V₂', hS', -, h31'⟩ := lin31Statement_holds G M Q Z B n V₁ V₂ hb hc hS (by omega)
  have SS := OddSetup.of_linSetup hc hS' h31'
  obtain ⟨hAZ, -, -⟩ := lin29_of_sit hs hA hAQ hAX
  have hxA : x ∈ QB A := (IsZConjugate.le_QB_iff H hA hs.conj).mpr hAX hs.mem
  have hZA : z' ∈ QB A := SS.Z_le_QB hA hAQ hz'
  have hZAbot : Z ⊓ A = ⊥ := by
    obtain ⟨g, rfl⟩ := hA
    exact inf_conjSubgroup_eq_bot_of_isTI H.ti hAZ
  obtain ⟨g, hg⟩ := hA
  have hx'Q : g⁻¹ * x * g ∈ Q := by
    rw [hg, QB_conj_eq H g] at hxA
    exact mem_conjSubgroup.mp hxA
  have hz''Q : g⁻¹ * z' * g ∈ Q := by
    rw [hg, QB_conj_eq H g] at hZA
    exact mem_conjSubgroup.mp hZA
  have hxQ : x ∉ Q := hs.notQ
  have hx1 : x ≠ 1 := hs.ne_one
  have hx'1 : g⁻¹ * x * g ≠ 1 := fun h => hx1 (by
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h]; group)
  have hz''1 : g⁻¹ * z' * g ≠ 1 := fun h => hz1 (by
    have : z' = g * (g⁻¹ * z' * g) * g⁻¹ := by group
    rw [this, h]; group)
  have hz''Z : g⁻¹ * z' * g ∉ Z := by
    intro h
    apply hz''1
    have hz'A : z' ∈ A := by
      rw [hg, mem_conjSubgroup]; simpa [mul_assoc] using h
    have : z' ∈ Z ⊓ A := ⟨hz', hz'A⟩
    rw [hZAbot, Subgroup.mem_bot] at this
    rw [this]; group
  have hx'cl : InZClass Z (g⁻¹ * x * g) := by
    have := (inZClass_conj_iff (Z := Z) (v := x) g⁻¹).mpr
      (inZClass_of_mem_root hs.conj hs.mem hs.ne_one)
    simpa using this
  have hwcl : InZClass Z (g⁻¹ * x * g * (g⁻¹ * z' * g)) := by
    have := (inZClass_conj_iff (Z := Z) (v := x * z') g⁻¹).mpr hcl
    simpa [mul_assoc] using this
  have hw1 : g⁻¹ * x * g * (g⁻¹ * z' * g) ≠ 1 := by
    intro h
    have h1 : x * z' = 1 := by
      have : x * z' = g * (g⁻¹ * x * g * (g⁻¹ * z' * g)) * g⁻¹ := by group
      rw [this, h]; group
    apply hxQ
    have : x = z'⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact Q.inv_mem (H.Z_normal.1 hz')
  set Y : Subgroup G := conjSubgroup g⁻¹ Z with hYdef
  have hY : IsZConjugate Z Y := ⟨g⁻¹, rfl⟩
  have hz''Y : g⁻¹ * z' * g ∈ Y := by
    rw [hYdef, mem_conjSubgroup]; simpa [mul_assoc] using hz'
  have hYZ : Y ≠ Z := fun h => hz''Z (h ▸ hz''Y)
  have hα' := linModuleStatement_holds G M Q Z B n V₁' V₂' hb hc hS' hn3 Y hY hYZ
  rcases (SS.p31 _ hz''Q hz''1).mp (inZClass_of_mem_root hY hz''Y hz''1) with hV | hV
  · obtain ⟨hYV, -, -⟩ := SS.root_le_V hY hz''Y hV hz''Z
    exact c4_core SS hxQ hx'Q hx'1 hz''Q hz''Z hV hx'cl hwcl hw1 (hα'.1 hYV)
  · obtain ⟨hYV, -, -⟩ := SS.symm.root_le_V hY hz''Y hV hz''Z
    exact c4_core SS.symm hxQ hx'Q hx'1 hz''Q hz''Z hV hx'cl hwcl hw1 (hα'.2 hYV)

theorem fixed_preimage (R : RestModel M Q Z n V₁ V₂) (hs : Sit M Q Z X x) (hx : x ∈ H0 M Z)
    (c4 : ∀ z' ∈ Z, InZClass Z (x * z') → z' = 1) {k : R.M₀.E}
    (hk : R.φ ⟨x, hx⟩ k = k) :
    ∃ k₀ ∈ Q ⊓ Subgroup.centralizer ({x} : Set G), R.M₀.π k₀ = k := by
  obtain ⟨q, hqQ, rfl⟩ := R.M₀.π_surj k
  have hx2 := hs.x_sq
  have H := R.hyp
  have hxQ : x * q * x⁻¹ ∈ Q := conj_mem_Q H hx.1 hqQ
  have hπ : R.M₀.π (x * q * x⁻¹) = R.M₀.π q := by rw [R.φπ ⟨x, hx⟩ q hqQ]; exact hk
  have hz : q⁻¹ * (x * q * x⁻¹) ∈ Z := (R.M₀.pi_eq_iff hqQ hxQ).mp hπ.symm
  have hcomm : ⁅x, q⁆ ∈ Z := by
    have e : ⁅x, q⁆ = q * (q⁻¹ * (x * q * x⁻¹)) * q⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, ← Z_central H hz hqQ]
    simpa using hz
  have hqC : q ∈ CQt Q Z (Subgroup.zpowers x) := by
    refine ⟨hqQ, fun t ht => ?_⟩
    rcases mem_zpowers_of_mul_self_eq_one hx2 ht with rfl | rfl
    · simpa using Z.one_mem
    · exact hcomm
  rw [cqt_eq_of_class hs c4] at hqC
  have hZle : Z ≤ Q ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro z hz
    refine ⟨H.Z_normal.1 hz, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := hs.x_cent (smith_1_12 hs) z hz
    calc z * x = (x * z * x⁻¹) * x := by rw [this]
      _ = x * z := by group
  have hqC' : q ∈ ((Q ⊓ Subgroup.centralizer ({x} : Set G)) ⊔ Z : Subgroup G) := hqC
  rw [sup_eq_left.mpr hZle] at hqC'
  exact ⟨q, hqC', rfl⟩

theorem img_D_mem_Nsp (R : RestModel M Q Z n V₁ V₂) (hs : Sit M Q Z X x) (hx : x ∈ H0 M Z)
    (hx2 : x * x = 1) (c4 : ∀ z' ∈ Z, InZClass Z (x * z') → z' = 1) {d : G}
    (hd : d ∈ Q ⊓ QB X) : R.M₀.π d ∈ R.Nsp hx := by
  have h12 := smith_1_12 hs
  obtain ⟨u, hu⟩ := exists_sub_of_orth_fixed R.M₀.B R.M₀.nondeg R.M₀.alt (R.φ ⟨x, hx⟩)
    (R.B_inv ⟨x, hx⟩) (v := R.M₀.π d) (by
      intro k hk
      obtain ⟨k₀, hk₀, rfl⟩ := fixed_preimage R hs hx c4 hk
      have hcomm := (smith_1_13_of_post12 hs h12).2.2.2.2 d hd k₀ hk₀
      exact (R.M₀.comm_iff_B R.gm.reg hd.1 hk₀.1).mp hcomm)
  exact (R.mem_Nsp hx _).mpr ⟨u, hu.symm⟩

theorem card_img_D (R : RestModel M Q Z n V₁ V₂) (hs : Sit M Q Z X x) :
    Nat.card ↥(R.M₀.img (Q ⊓ QB X)) = Nat.card ↥(Q ⊓ QB X) := by
  have h12 := smith_1_12 hs
  have hZX := Z_inf_QB_eq_bot hs h12
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun d : ↥(Q ⊓ QB X) => (⟨R.M₀.π d, ⟨d, d.2, d.2.1, rfl⟩⟩ : ↥(R.M₀.img (Q ⊓ QB X)))) ⟨?_, ?_⟩)
  · intro d d' h
    have h1 : R.M₀.π d = R.M₀.π d' := congrArg Subtype.val h
    have h2 : (d : G)⁻¹ * d' ∈ Z := (R.M₀.pi_eq_iff d.2.1 d'.2.1).mp h1
    have h3 : (d : G)⁻¹ * d' ∈ QB X := (QB X).mul_mem ((QB X).inv_mem d.2.2) d'.2.2
    have h4 : (d : G)⁻¹ * d' ∈ Z ⊓ QB X := ⟨h2, h3⟩
    rw [hZX, Subgroup.mem_bot] at h4
    exact Subtype.ext (inv_mul_eq_one.mp h4)
  · rintro ⟨e, d, hd, hdQ, rfl⟩
    exact ⟨⟨d, hd⟩, rfl⟩

theorem rest_first_core_R (R : RestModel M Q Z n V₁ V₂) (hb : Smith1981Below (Nat.card G))
    (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) (hs : Sit M Q Z X x)
    (hx : x ∈ H0 M Z) {A : Subgroup G}
    (hA : IsZConjugate Z A) (hAQ : A ≤ Q) (hAX : A ≤ QB X) (hAV : A ≤ V₁) :
    ∀ e ∈ R.Nsp hx, e ∈ R.M₀.img (Q ⊓ QB X) := by
  have H := hc.hyp
  have h12 := smith_1_12 hs
  have hZQ : Z ≤ Q := H.Z_normal.1
  obtain ⟨hAZ, -, hXLA⟩ := lin29_of_sit hs hA hAQ hAX
  have hcA : Ctx M Q Z A := ⟨H, hA, hAQ, hAZ⟩
  have hxLB : x ∈ LB M Q A := hXLA hs.mem
  obtain ⟨-, htr⟩ := LinSetup.transv_of_conj hc hS hn hcA
  obtain ⟨hd₁, hd₂, hAc⟩ := htr x hxLB hs.notQ
  obtain ⟨hcn₁, hcn₂⟩ := LinSetup.conj_eq_of_le_V₁ hc hS hn hcA hAV hxLB
  have hxn₁ : x ∈ Subgroup.normalizer (V₁ : Set G) := conjSubgroup_eq_self_iff.mp hcn₁
  have hxn₂ : x ∈ Subgroup.normalizer (V₂ : Set G) := conjSubgroup_eq_self_iff.mp hcn₂
  have hx2 := hs.x_sq
  have c4 := c4_of_A hb hc hS hn hs hA hAQ hAX
  have hqK : Nat.card R.K = Nat.card Z := R.gm.card
  have hq1 : 1 < Nat.card Z := by have := H.q4; omega
  have hz0 : 0 < Nat.card Z := Nat.card_pos
  have hP₁ : Nat.card ↥(R.Nsp hx ⊓ R.W₁) = Nat.card R.K := by
    have h := R.card_comm_sup_V₁ hx hx2 hxn₁ hxn₂
    have hd : Nat.card ↥(⁅V₁, Subgroup.zpowers x⁆ ⊔ Z) = Nat.card Z ^ (1 + 1) := hd₁
    rw [h] at hd
    rw [hqK]
    have : Nat.card ↥(R.Nsp hx ⊓ R.W₁) * Nat.card Z = Nat.card Z * Nat.card Z := by
      rw [hd]; ring
    exact Nat.eq_of_mul_eq_mul_right hz0 this
  have hP₂ : Nat.card ↥(R.Nsp hx ⊓ R.W₂) = Nat.card R.K := by
    have h := R.card_comm_sup_V₂ hx hx2 hxn₁ hxn₂
    have hd : Nat.card ↥(⁅V₂, Subgroup.zpowers x⁆ ⊔ Z) = Nat.card Z ^ (1 + 1) := hd₂
    rw [h] at hd
    rw [hqK]
    have : Nat.card ↥(R.Nsp hx ⊓ R.W₂) * Nat.card Z = Nat.card Z * Nat.card Z := by
      rw [hd]; ring
    exact Nat.eq_of_mul_eq_mul_right hz0 this
  obtain ⟨b, hb0, -, hAb, -, -⟩ := hcA.dictB R.gm
  have hbA : b ∈ R.M₀.img A := (hAb b).mpr ⟨1, by rw [one_smul]⟩
  obtain ⟨a, haA, haQ, hab⟩ := hbA
  have hbW₁ : b ∈ R.W₁ :=
    (R.memW₁ b).mpr (R.M₀.img_mono hAV ⟨a, haA, haQ, hab⟩)
  have hbN : b ∈ R.Nsp hx := by
    have := ((R.mem_comm_sup_iff hx hx2).mp (hAc haA)).2
    rwa [hab] at this
  have hbP : b ∈ R.Nsp hx ⊓ R.W₁ := ⟨hbN, hbW₁⟩
  obtain ⟨β, hβP, hβ0⟩ : ∃ β ∈ R.Nsp hx ⊓ R.W₂, β ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : Subsingleton ↥(R.Nsp hx ⊓ R.W₂) :=
      ⟨fun u v => Subtype.ext ((hcon _ u.2).trans (hcon _ v.2).symm)⟩
    have h1 : Nat.card ↥(R.Nsp hx ⊓ R.W₂) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨⟨0, Submodule.zero_mem _⟩⟩⟩
    rw [hP₂, hqK] at h1
    omega
  have hN₁ : ∀ u ∈ R.W₁, ∃ s : R.K, R.φ ⟨x, hx⟩ u - u = s • b := by
    intro u hu
    have hmem : R.φ ⟨x, hx⟩ u - u ∈ R.Nsp hx ⊓ R.W₁ :=
      ⟨(R.mem_Nsp hx _).mpr ⟨u, rfl⟩, R.W₁.sub_mem (R.φ_mem_W₁ _ hxn₁ hu) hu⟩
    obtain ⟨s, hs'⟩ := exists_eq_smul_of_card hP₁ hbP hb0 hmem
    exact ⟨s, hs'⟩
  have hN₂ : ∀ u ∈ R.W₂, ∃ s : R.K, R.φ ⟨x, hx⟩ u - u = s • β := by
    intro u hu
    have hmem : R.φ ⟨x, hx⟩ u - u ∈ R.Nsp hx ⊓ R.W₂ :=
      ⟨(R.mem_Nsp hx _).mpr ⟨u, rfl⟩, R.W₂.sub_mem (R.φ_mem_W₂ _ hxn₂ hu) hu⟩
    obtain ⟨s, hs'⟩ := exists_eq_smul_of_card hP₂ hβP hβ0 hmem
    exact ⟨s, hs'⟩
  have hu₁ : ∃ u ∈ R.W₁, R.φ ⟨x, hx⟩ u - u = b := R.exists_pre_W₁ hx hxn₁ hxn₂ hbN hbW₁
  have hu₂ : ∃ u ∈ R.W₂, R.φ ⟨x, hx⟩ u - u = β :=
    R.exists_pre_W₂ hx hxn₁ hxn₂ hβP.1 hβP.2
  set Dt : AddSubgroup R.M₀.E := R.M₀.img (Q ⊓ QB X) with hDtdef
  have hDtN : ∀ e ∈ Dt, e ∈ R.Nsp hx := by
    rintro e ⟨d, hd, hdQ, rfl⟩
    exact img_D_mem_Nsp R hs hx hx2 c4 hd
  have hdecomp : ∀ e ∈ R.Nsp hx, ∃ s t : R.K, e = s • b + t • β := by
    intro e he
    obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := R.exists_decomp_Nsp hx hxn₁ hxn₂ he
    obtain ⟨s, hs'⟩ := exists_eq_smul_of_card hP₁ hbP hb0 he₁
    obtain ⟨t, ht⟩ := exists_eq_smul_of_card hP₂ hβP hβ0 he₂
    exact ⟨s, t, by rw [hs', ht]⟩
  have hDt : ∀ e ∈ Dt, ∃ s t : R.K, e = s • b + t • β := fun e he => hdecomp e (hDtN e he)
  have hcDt : ∀ s : R.K, s • b ∈ Dt := fun s =>
    R.M₀.img_mono (le_inf hAQ hAX) ((hAb _).mpr ⟨s, rfl⟩)
  have hLxH : Lx M X ≤ H0 M Z := Lx_le_H0 hs h12
  have h13 := smith_1_13_of_post12 hs h12
  have hLxC : ∀ l ∈ Lx M X, ∀ d ∈ Q ⊓ QB X, d * l = l * d := fun l hl d hd =>
    Subgroup.mem_centralizer_iff.mp (h13.2.2.1 hl) d hd
  obtain ⟨a₀, ha₀A, ha₀1, ha₀Z⟩ := exists_mem_ne_Z H hA hAZ
  have hl_norm : ∀ l ∈ Lx M X, l ∈ Subgroup.normalizer (V₁ : Set G) ∧
      l ∈ Subgroup.normalizer (V₂ : Set G) := by
    intro l hl
    have hcomm : a₀ * l = l * a₀ := hLxC l hl a₀ ⟨hAQ ha₀A, hAX ha₀A⟩
    rcases linSwapStatement_holds G M Q Z B n V₁ V₂ hc hS hn l (hLxH hl) with h | h
    · exact ⟨conjSubgroup_eq_self_iff.mp h.1, conjSubgroup_eq_self_iff.mp h.2⟩
    · exfalso
      have ha₁ : a₀ ∈ V₂ := by
        have : a₀ ∈ conjSubgroup l V₁ := by
          rw [mem_conjSubgroup]
          have e : l⁻¹ * a₀ * l = a₀ := by
            calc l⁻¹ * a₀ * l = l⁻¹ * (a₀ * l) := by group
              _ = l⁻¹ * (l * a₀) := by rw [hcomm]
              _ = a₀ := by group
          rw [e]; exact hAV ha₀A
        rw [h.1] at this; exact this
      apply ha₀Z
      rw [← R.V₁₂]; exact ⟨hAV ha₀A, ha₁⟩
  set ψ : ↥(Lx M X) →* (R.M₀.E ≃ₗ[R.K] R.M₀.E) := R.φ.comp (Subgroup.inclusion hLxH) with hψ
  have hl_fix : ∀ l : ↥(Lx M X), ψ l b = b := by
    intro l
    have hcomm : a * (l : G) = (l : G) * a := hLxC l l.2 a ⟨hAQ haA, hAX haA⟩
    have e : (l : G) * a * (l : G)⁻¹ = a := mul_inv_eq_iff_eq_mul.mpr hcomm.symm
    have := R.φπ ⟨(l : G), hLxH l.2⟩ a haQ
    rw [e, hab] at this
    exact this.symm
  have hl_D : ∀ l : ↥(Lx M X), ∀ v, R.φ ⟨x, hx⟩ v = v → ψ l v - v ∈ Dt := by
    intro l v hv
    obtain ⟨k₀, hk₀, rfl⟩ := fixed_preimage R hs hx c4 hv
    have hl := l.2
    have hlM : (l : G) ∈ M := (hLxH hl).1
    have hk₀Kx : k₀ ∈ Kx Q X := by rw [Kx_eq hs h12]; exact hk₀
    have hcomD : ⁅k₀, (l : G)⁆ ∈ Q ⊓ QB X :=
      h13.1 (Subgroup.commutator_mem_commutator hk₀Kx hl)
    have hw : (l : G) * k₀⁻¹ * (l : G)⁻¹ ∈ Q := conj_mem_Q H hlM (Q.inv_mem hk₀.1)
    have hπc : R.M₀.π ⁅k₀, (l : G)⁆ = R.M₀.π k₀ - ψ l (R.M₀.π k₀) := by
      have e : ⁅k₀, (l : G)⁆ = k₀ * ((l : G) * k₀⁻¹ * (l : G)⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e, R.M₀.π_mul k₀ hk₀.1 _ hw, R.φπ ⟨(l : G), hLxH hl⟩ k₀⁻¹ (Q.inv_mem hk₀.1),
        Tim79.QuadModel.pi_inv R.M₀ hk₀.1, map_neg, sub_eq_add_neg]
      rfl
    have hmem : R.M₀.π k₀ - ψ l (R.M₀.π k₀) ∈ Dt := by
      rw [← hπc]; exact ⟨⁅k₀, (l : G)⁆, hcomD, hcomD.1, rfl⟩
    have := Dt.neg_mem hmem
    simpa using this
  have hSetFin : ∀ (Sset : Set R.M₀.E), Sset = Set.range
      (fun p : R.K × R.K => p.1 • b + p.2 • β) → Nat.card ↥Sset ≤ Nat.card Z ^ 2 := by
    intro Sset hSset
    subst hSset
    have h1 := Nat.card_le_card_of_surjective
      (Set.rangeFactorization (fun p : R.K × R.K => p.1 • b + p.2 • β))
      Set.rangeFactorization_surjective
    rw [Nat.card_prod, hqK] at h1
    rw [pow_two]
    exact h1
  have hβDt : ∀ t : R.K, t • β ∈ Dt := by
    by_cases hbr : ∀ l : ↥(Lx M X), ∀ u ∈ R.W₁, ∃ s : R.K, ψ l u - u = s • b
    ·
      have hΓ := la_card_le R.M₀.B R.M₀.nondeg R.M₀.alt R.W₁ R.W₂ R.hsup R.hint R.iso₁ R.iso₂
        hbW₁ hb0 ψ.range (by
          rintro g ⟨l, rfl⟩
          exact ⟨fun u hu => R.φ_mem_W₁ _ (hl_norm l l.2).1 hu,
            fun u hu => R.φ_mem_W₂ _ (hl_norm l l.2).2 hu,
            R.B_inv ⟨(l : G), hLxH l.2⟩, hl_fix l, hbr l⟩)
      have hDLx : Q ⊓ QB X ≤ Lx M X := fun d hd => ⟨hd.2, H.Q_normal.1 hd.1⟩
      have hker : ψ.ker = (Q ⊓ QB X).subgroupOf (Lx M X) := by
        ext l
        simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        constructor
        · intro h
          exact ⟨(R.φker ⟨(l : G), hLxH l.2⟩).mp h, (Subgroup.mem_inf.mp l.2).1⟩
        · intro h
          exact (R.φker ⟨(l : G), hLxH l.2⟩).mpr h.1
      have hcardL : Nat.card ↥(Lx M X) = Nat.card ↥ψ.range * Nat.card ↥(Q ⊓ QB X) := by
        have h1 : Nat.card ↥ψ.ker * ψ.ker.index = Nat.card ↥(Lx M X) :=
          Subgroup.card_mul_index ψ.ker
        rw [Subgroup.index_ker] at h1
        have h2 : Nat.card ↥ψ.ker = Nat.card ↥(Q ⊓ QB X) := by
          rw [hker]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDLx).toEquiv
        rw [← h1, h2, mul_comm]
      have hmain : Nat.card Z ^ (n - 1) ≤ Nat.card ↥(Q ⊓ QB X) := by
        have h1 := card_Lx_ge hc hS hn hs hA hAQ hAX
        have hqn : 0 < Nat.card Z ^ n := pow_pos hz0 n
        have h2 : Nat.card Z ^ n * Nat.card Z ^ (n - 1) ≤
            Nat.card Z ^ n * Nat.card ↥(Q ⊓ QB X) := by
          calc Nat.card Z ^ n * Nat.card Z ^ (n - 1)
              = Nat.card Z ^ (2 * n - 2) * Nat.card Z := by
                rw [← pow_add, ← pow_succ]; congr 1; omega
            _ ≤ Nat.card ↥(Lx M X) * Nat.card Z := Nat.mul_le_mul_right _ h1
            _ = (Nat.card ↥ψ.range * Nat.card Z) * Nat.card ↥(Q ⊓ QB X) := by
                rw [hcardL]; ring
            _ ≤ Nat.card ↥R.W₁ * Nat.card ↥(Q ⊓ QB X) :=
                Nat.mul_le_mul_right _ (by rw [← hqK]; exact hΓ)
            _ = Nat.card Z ^ n * Nat.card ↥(Q ⊓ QB X) := by rw [R.card_W₁]
        exact Nat.le_of_mul_le_mul_left h2 hqn
      have hq2 : Nat.card Z ^ 2 ≤ Nat.card Z ^ (n - 1) :=
        Nat.pow_le_pow_right hz0 (by omega)
      have hDtcard : Nat.card Z ^ 2 ≤ Nat.card ↥Dt := by
        rw [hDtdef, card_img_D R hs]
        exact hq2.trans hmain
      set Sset : Set R.M₀.E := Set.range (fun p : R.K × R.K => p.1 • b + p.2 • β) with hSdef
      have hDS : (Dt : Set R.M₀.E) ⊆ Sset := by
        intro e he
        obtain ⟨s, t, rfl⟩ := hDt e he
        exact ⟨(s, t), rfl⟩
      have hSle := hSetFin Sset hSdef
      have hnc : Sset.ncard ≤ (Dt : Set R.M₀.E).ncard := by
        rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
        exact hSle.trans hDtcard
      have heq := Set.eq_of_subset_of_ncard_le hDS hnc (Set.toFinite _)
      intro t
      have : t • β ∈ Sset := ⟨(0, t), by simp⟩
      rw [← heq] at this
      exact this
    · push Not at hbr
      obtain ⟨l, u, hu, hnot⟩ := hbr
      have hdich := la_dichotomy R.M₀.B R.M₀.nondeg R.M₀.alt R.W₁ R.W₂ R.hsup R.hint R.iso₁
        R.iso₂ (R.φ ⟨x, hx⟩) (ψ l) (R.B_inv ⟨x, hx⟩) (R.B_inv ⟨(l : G), hLxH l.2⟩)
        (R.φ_sq ⟨x, hx⟩ hx2) (fun u hu => R.φ_mem_W₁ _ hxn₁ hu)
        (fun u hu => R.φ_mem_W₂ _ hxn₂ hu)
        (fun u hu => R.φ_mem_W₁ _ (hl_norm l l.2).1 hu)
        (fun u hu => R.φ_mem_W₂ _ (hl_norm l l.2).2 hu)
        hbW₁ hβP.2 hb0 hβ0 hN₁ hN₂ hu₁ hu₂ (hl_fix l) Dt hDt (hl_D l)
      rcases hdich with h | h
      · obtain ⟨s, hs'⟩ := h u hu
        exact absurd hs' (hnot s)
      · exact h
  intro e he
  obtain ⟨s, t, rfl⟩ := hdecomp e he
  exact Dt.add_mem (hcDt s) (hβDt t)

theorem rest_first_core (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) (hs : Sit M Q Z X x) {A : Subgroup G}
    (hA : IsZConjugate Z A) (hAQ : A ≤ Q) (hAX : A ≤ QB X) (hAV : A ≤ V₁) :
    (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x⁆ ⊔ Z := by
  have H := hc.hyp
  have h12 := smith_1_12 hs
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hx2 := hs.x_sq
  have hx : x ∈ H0 M Z := h12.1 hs.mem
  have c4 := c4_of_A hb hc hS hn hs hA hAQ hAX
  obtain ⟨R⟩ := exists_restModel hc hS hn
  have hcore := rest_first_core_R R hb hc hS hn hs hx hA hAQ hAX hAV
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    intro d hd
    exact (R.mem_comm_sup_iff hx hx2).mpr ⟨hd.1, img_D_mem_Nsp R hs hx hx2 c4 hd⟩
  · intro y hy
    obtain ⟨hyQ, hyN⟩ := (R.mem_comm_sup_iff hx hx2).mp hy
    obtain ⟨d, hd, hdQ, hdπ⟩ := hcore _ hyN
    have hz : d⁻¹ * y ∈ Z := (R.M₀.pi_eq_iff hdQ hyQ).mp hdπ
    have hy' : y = d * (d⁻¹ * y) := by group
    rw [hy']
    exact Subgroup.mul_mem_sup hd hz

end Sit

end CFSG.RankThree.GF2n.Smith81
