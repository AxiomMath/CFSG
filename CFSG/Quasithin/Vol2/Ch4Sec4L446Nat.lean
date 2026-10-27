module

public import CFSG.Quasithin.H13.StatementsVocab
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Background.OperatorJordanHolder
public import CFSG.Quasithin.Background.A4
public import CFSG.Quasithin.Vol2.Ch4Sec4Inputs

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative Matrix Pointwise

variable {G : Type} [Group G]

theorem le_normalizer_iSup_of_forall {ι : Sort*} {L : Subgroup G} {W : ι → Subgroup G}
    (hW : ∀ i, L ≤ Subgroup.normalizer (W i : Set G)) :
    L ≤ Subgroup.normalizer ((⨆ i, W i : Subgroup G) : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  exact iSup_congr fun i => Subgroup.mem_normalizer_iff_map_conj_eq.mp (hW i hl)

theorem le_normalizer_sup_of_le {L A B : Subgroup G} (hA : L ≤ Subgroup.normalizer (A : Set G))
    (hB : L ≤ Subgroup.normalizer (B : Set G)) :
    L ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hl),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hl)]

theorem eq_of_inv_mul_mem {X₀ C : Subgroup G} (hXC : X₀ ⊓ C = ⊥) {w x y : G} (hx : x ∈ X₀)
    (hy : y ∈ X₀) (h1 : x⁻¹ * w ∈ C) (h2 : y⁻¹ * w ∈ C) : x = y := by
  have h3 : y⁻¹ * x ∈ C := by
    have := C.mul_mem h2 (C.inv_mem h1)
    simpa [mul_assoc] using this
  have h4 : y⁻¹ * x ∈ X₀ ⊓ C := ⟨X₀.mul_mem (X₀.inv_mem hy) hx, h3⟩
  rw [hXC, Subgroup.mem_bot] at h4
  exact (inv_mul_eq_one.mp h4).symm

section Abelian

variable {V : Subgroup G} (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
include hV

theorem exists_mul_of_mem_sup_of_comm {A B : Subgroup G} (hA : A ≤ V) (hB : B ≤ V) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hAB : A ≤ Subgroup.normalizer (B : Set G) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [hV a (hA ha) b (hB hb), mul_inv_cancel_right]
      exact hb
    · intro hb
      have hbV : b ∈ V := by
        have := V.mul_mem (V.mul_mem (V.inv_mem (hA ha)) (hB hb)) (hA ha)
        simpa [mul_assoc] using this
      rwa [hV a (hA ha) b hbV, mul_inv_cancel_right] at hb
  have hx' : x ∈ ((A : Set G) * (B : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hAB]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem inf_sup_eq_bot_of_comm {X W B : Subgroup G} (hW : W ≤ V) (hB : B ≤ V)
    (h1 : X ⊓ B = ⊥) (h2 : W ⊓ (X ⊔ B) = ⊥) : X ⊓ (W ⊔ B) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxX, hxWB⟩
  obtain ⟨w, hw, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_comm hV hW hB hxWB
  have hwXB : w ∈ X ⊔ B := by
    have e : w = (w * b) * b⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem_sup hxX (B.inv_mem hb)
  have hw1 : w = 1 := by
    have : w ∈ W ⊓ (X ⊔ B) := ⟨hw, hwXB⟩
    rwa [h2, Subgroup.mem_bot] at this
  subst hw1
  rw [one_mul] at hxX ⊢
  have : b ∈ X ⊓ B := ⟨hxX, hb⟩
  rwa [h1] at this

theorem exists_finset_compl {L X : Subgroup G} {k : ℕ} {W : Fin k → Subgroup G}
    (hWV : ∀ i, W i ≤ V) (hLW : ∀ i, L ≤ Subgroup.normalizer (W i : Set G))
    (hirr : ∀ i, ∀ Y : Subgroup G, Y ≤ W i → L ≤ Subgroup.normalizer (Y : Set G) →
      Y = ⊥ ∨ Y = W i)
    (hsup : ⨆ i, W i = V) (hXV : X ≤ V) (hLX : L ≤ Subgroup.normalizer (X : Set G)) :
    ∃ S : Finset (Fin k), X ⊓ (⨆ i ∈ S, W i) = ⊥ ∧ X ⊔ (⨆ i ∈ S, W i) = V := by
  classical
  set P := (Finset.univ : Finset (Finset (Fin k))).filter
    (fun S => X ⊓ (⨆ i ∈ S, W i) = ⊥) with hPdef
  have hP : P.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image P (fun S : Finset (Fin k) => S.card) hP
  have hS' : X ⊓ (⨆ i ∈ S, W i) = ⊥ := (Finset.mem_filter.mp hS).2
  set WS := ⨆ i ∈ S, W i with hWS
  have hWSV : WS ≤ V := iSup₂_le fun i _ => hWV i
  have hLWS : L ≤ Subgroup.normalizer (WS : Set G) :=
    le_normalizer_iSup_of_forall fun i => le_normalizer_iSup_of_forall fun _ => hLW i
  have hj : ∀ j, W j ≤ X ⊔ WS := by
    intro j
    by_cases hjS : j ∈ S
    · have hjWS : W j ≤ WS := le_iSup₂_of_le (f := fun i (_ : i ∈ S) => W i) j hjS le_rfl
      exact hjWS.trans le_sup_right
    · rcases hirr j (W j ⊓ (X ⊔ WS)) inf_le_left
        (fun l hl => A4.mem_normalizer_inf (hLW j hl) (le_normalizer_sup_of_le hLX hLWS hl))
        with h0 | h1
      · exfalso
        have hins : X ⊓ (⨆ i ∈ insert j S, W i) = ⊥ := by
          rw [Finset.iSup_insert]
          exact inf_sup_eq_bot_of_comm hV (hWV j) hWSV hS' h0
        have := hmax (insert j S) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hins⟩)
        rw [Finset.card_insert_of_notMem hjS] at this
        omega
      · rw [← h1]
        exact inf_le_right
  refine ⟨S, hS', le_antisymm (_root_.sup_le hXV hWSV) ?_⟩
  rw [← hsup]
  exact iSup_le hj

theorem exists_proj_of_compl {X₀ C W : Subgroup G} (hX₀ : X₀ ≤ V) (hC : C ≤ V) (hW : W ≤ V)
    (hXC : X₀ ⊓ C = ⊥) (hsup : X₀ ⊔ C = V) :
    ∃ p : ↥W →* ↥X₀, ∀ w : ↥W, ((p w : ↥X₀) : G)⁻¹ * w ∈ C := by
  have hex : ∀ w : ↥W, ∃ x : ↥X₀, (x : G)⁻¹ * w ∈ C := fun w => by
    have hw : (w : G) ∈ X₀ ⊔ C := by
      rw [hsup]
      exact hW w.2
    obtain ⟨x, hx, c, hc, hxc⟩ := exists_mul_of_mem_sup_of_comm hV hX₀ hC hw
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [← hxc]
    simpa using hc
  choose f hf using hex
  have hmul : ∀ a b : ↥W, f (a * b) = f a * f b := by
    intro a b
    refine Subtype.ext (eq_of_inv_mul_mem hXC (f (a * b)).2 (f a * f b).2 (hf (a * b)) ?_)
    have hfa := hX₀ (f a).2
    have hfb := hX₀ (f b).2
    have e : ((f a * f b : ↥X₀) : G)⁻¹ * ((a * b : ↥W) : G) =
        ((f a : G)⁻¹ * a) * ((f b : G)⁻¹ * b) := by
      simp only [Subgroup.coe_mul, mul_inv_rev]
      have h1 : (f b : G)⁻¹ * ((f a : G)⁻¹ * a) = ((f a : G)⁻¹ * a) * (f b : G)⁻¹ :=
        hV _ (V.inv_mem hfb) _ (V.mul_mem (V.inv_mem hfa) (hW a.2))
      calc (f b : G)⁻¹ * (f a : G)⁻¹ * (a * b) = ((f b : G)⁻¹ * ((f a : G)⁻¹ * a)) * b := by
            group
        _ = (((f a : G)⁻¹ * a) * (f b : G)⁻¹) * b := by rw [h1]
        _ = ((f a : G)⁻¹ * a) * ((f b : G)⁻¹ * b) := by group
    rw [e]
    exact C.mul_mem (hf a) (hf b)
  have hone : f 1 = 1 := by
    refine Subtype.ext (eq_of_inv_mul_mem hXC (f 1).2 (1 : ↥X₀).2 (hf 1) ?_)
    simp
  exact ⟨{ toFun := f, map_one' := hone, map_mul' := hmul }, hf⟩

end Abelian

@[expose] def IsLEquiv (L : Subgroup G) {A B : Subgroup G} (φ : ↥A ≃* ↥B) : Prop :=
  ∀ l ∈ L, ∀ a a' : ↥A, (a' : G) = l * a * l⁻¹ → ((φ a' : ↥B) : G) = l * (φ a : G) * l⁻¹

theorem IsLEquiv.symm {L A B : Subgroup G} {φ : ↥A ≃* ↥B} (h : IsLEquiv L φ)
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) : IsLEquiv L φ.symm := by
  intro l hl b b' hb'
  have ha : l * ((φ.symm b : ↥A) : G) * l⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp (hLA hl) _).mp (φ.symm b).2
  have h1 := h l hl (φ.symm b) ⟨_, ha⟩ rfl
  rw [MulEquiv.apply_symm_apply, ← hb'] at h1
  have h2 : φ ⟨_, ha⟩ = b' := Subtype.ext h1
  rw [← h2, MulEquiv.symm_apply_apply]

theorem IsLEquiv.trans {L A B C : Subgroup G} {φ : ↥A ≃* ↥B} {ψ : ↥B ≃* ↥C} (hφ : IsLEquiv L φ)
    (hψ : IsLEquiv L ψ) : IsLEquiv L (φ.trans ψ) := by
  intro l hl a a' ha'
  exact hψ l hl (φ a) (φ a') (hφ l hl a a' ha')

@[expose] noncomputable def quotBotEquiv (A : Subgroup G) :
    ↥A ⧸ (⊥ : Subgroup G).subgroupOf A ≃* ↥A :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf A)).trans QuotientGroup.quotientBot

theorem quotBotEquiv_mk (A : Subgroup G) (a : ↥A) :
    quotBotEquiv A (QuotientGroup.mk a) = a := rfl

theorem isXSectionIso₂_of_isLEquiv {L A B : Subgroup G} {φ : ↥A ≃* ↥B} (h : IsLEquiv L φ) :
    IsXSectionIso₂ L A ⊥ B ⊥ := by
  have hnA : ((⊥ : Subgroup G).subgroupOf A).Normal := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  have hnB : ((⊥ : Subgroup G).subgroupOf B).Normal := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  refine ⟨hnA, hnB, (quotBotEquiv A).trans (φ.trans (quotBotEquiv B).symm), ?_⟩
  intro x hx j k hj hk hjk
  have h1 : φ j = k := by
    have := congrArg (quotBotEquiv B) hjk
    simpa [quotBotEquiv_mk] using this
  have h2 : φ ⟨x * j * x⁻¹, hj⟩ = ⟨x * k * x⁻¹, hk⟩ := by
    apply Subtype.ext
    rw [h x hx j ⟨x * j * x⁻¹, hj⟩ rfl, h1]
  show (quotBotEquiv B).symm (φ (quotBotEquiv A (QuotientGroup.mk ⟨x * j * x⁻¹, hj⟩))) =
    QuotientGroup.mk ⟨x * k * x⁻¹, hk⟩
  rw [quotBotEquiv_mk, h2, MulEquiv.symm_apply_eq, quotBotEquiv_mk]

theorem quotBotEquiv_symm_apply (A : Subgroup G) (a : ↥A) :
    (quotBotEquiv A).symm a = QuotientGroup.mk a := by
  rw [MulEquiv.symm_apply_eq, quotBotEquiv_mk]

theorem exists_isLEquiv_of_isXSectionIso₂ {L A B : Subgroup G}
    (hLB : L ≤ Subgroup.normalizer (B : Set G)) (h : IsXSectionIso₂ L A ⊥ B ⊥) :
    ∃ φ : ↥A ≃* ↥B, IsLEquiv L φ := by
  obtain ⟨hnA, hnB, e, he⟩ := h
  refine ⟨((quotBotEquiv A).symm.trans e).trans (quotBotEquiv B), ?_⟩
  have hφ : ∀ x : ↥A, (((quotBotEquiv A).symm.trans e).trans (quotBotEquiv B)) x =
      quotBotEquiv B (e (QuotientGroup.mk x)) := fun x => by
    simp only [MulEquiv.trans_apply, quotBotEquiv_symm_apply]
  intro l hl a a' ha'
  set k := quotBotEquiv B (e (QuotientGroup.mk a)) with hk
  have hk' : e (QuotientGroup.mk a) = QuotientGroup.mk k := by
    rw [← quotBotEquiv_symm_apply B k, hk, MulEquiv.symm_apply_apply]
  have hkB : l * (k : G) * l⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hLB hl) _).mp k.2
  have haA : l * (a : G) * l⁻¹ ∈ A := ha' ▸ a'.2
  have h1 := he l hl a k haA hkB hk'
  have ha'' : a' = ⟨l * a * l⁻¹, haA⟩ := Subtype.ext ha'
  rw [hφ, hφ, ha'', h1, quotBotEquiv_mk]

theorem realizes_of_isLEquiv {L A B : Subgroup G} [IsMulCommutative ↥A] [IsMulCommutative ↥B]
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) (hLB : L ≤ Subgroup.normalizer (B : Set G))
    {φ : ↥A ≃* ↥B} (hφ : IsLEquiv L φ) {D : FFModel} (h : D.Realizes (autOn L A) ⊤ ⊥) :
    D.Realizes (autOn L B) ⊤ ⊥ := by
  have hconj : ∀ g : G, g ∈ L → ∀ (hgA : g ∈ Subgroup.normalizer (A : Set G))
      (hgB : g ∈ Subgroup.normalizer (B : Set G)),
      MulAut.congr φ (conjAct A ⟨g, hgA⟩) = conjAct B ⟨g, hgB⟩ := by
    intro g hg hgA hgB
    ext b
    simp only [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hφ g hg (φ.symm b) ((conjAct A ⟨g, hgA⟩) (φ.symm b)) (Setup.coe_conjAct_apply _ _),
      MulEquiv.apply_symm_apply, Setup.coe_conjAct_apply]
  have himage : (autOn L A).map (MulAut.congr φ).toMonoidHom = autOn L B := by
    ext ψ
    constructor
    · rintro ⟨χ, hχ, rfl⟩
      obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.mp hχ
      exact Setup.mem_autOn_iff.mpr ⟨⟨g, hLB hg⟩, hg, (hconj g hg g.2 (hLB hg)).symm⟩
    · intro hψ
      obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.mp hψ
      exact ⟨conjAct A ⟨g, hLA hg⟩, Setup.mem_autOn_iff.mpr ⟨⟨g, hLA hg⟩, hg, rfl⟩,
        hconj g hg (hLA hg) g.2⟩
  obtain ⟨π, hsurj, -, hkersec, -, -, hsec, hker, β, hβs, hβk, hβe⟩ := h
  set e : ↥(autOn L A) ≃* ↥(autOn L B) :=
    ((MulAut.congr φ).subgroupMap (autOn L A)).trans (MulEquiv.subgroupCongr himage) with he
  have hecoe : ∀ χ : ↥(autOn L A), ((e χ : ↥(autOn L B)) : MulAut ↥B) = MulAut.congr φ χ :=
    fun _ => rfl
  set τ : ↥(⊤ : Subgroup ↥B) ≃* ↥(⊤ : Subgroup ↥A) :=
    (Subgroup.topEquiv.trans φ.symm).trans Subgroup.topEquiv.symm with hτ
  have hτcoe : ∀ u : ↥(⊤ : Subgroup ↥B), ((τ u : ↥(⊤ : Subgroup ↥A)) : ↥A) = φ.symm u :=
    fun _ => rfl
  refine ⟨e.toMonoidHom.comp π, ⟨e.surjective.comp hsurj, bot_le, hkersec, fun _ _ _ => trivial,
    ?_, hsec, hker, β.comp τ.toMonoidHom, hβs.comp τ.surjective, ?_, ?_⟩⟩
  · intro k z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro u
    show β (τ u) = 1 ↔ _
    rw [hβk, Subgroup.mem_bot, Subgroup.mem_bot, hτcoe, MulEquiv.map_eq_one_iff]
  · intro γ u m hu hm hum
    have h1 : τ ⟨((e (π γ) : ↥(autOn L B)) : MulAut ↥B) (u : ↥B), hu⟩ =
        ⟨((π γ : ↥(autOn L A)) : MulAut ↥A) ((τ u : ↥(⊤ : Subgroup ↥A)) : ↥A), trivial⟩ := by
      apply Subtype.ext
      show φ.symm (((e (π γ) : ↥(autOn L B)) : MulAut ↥B) (u : ↥B)) =
        ((π γ : ↥(autOn L A)) : MulAut ↥A) (φ.symm (u : ↥B))
      rw [hecoe, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    show β (τ ⟨((e (π γ) : ↥(autOn L B)) : MulAut ↥B) (u : ↥B), hu⟩) = _
    rw [h1]
    exact hβe γ (τ u) m trivial hm hum

theorem binaryNaturalSL_of_isLEquiv {L A B : Subgroup G} [IsMulCommutative ↥A]
    [IsMulCommutative ↥B] (hLA : L ≤ Subgroup.normalizer (A : Set G))
    (hLB : L ≤ Subgroup.normalizer (B : Set G)) {φ : ↥A ≃* ↥B} (hφ : IsLEquiv L φ) {d a : ℕ}
    (h : BinaryNaturalSL (autOn L A) ⊤ ⊥ d a) : BinaryNaturalSL (autOn L B) ⊤ ⊥ d a := by
  obtain ⟨K, hK, hKf, hc, hr⟩ := h
  exact ⟨K, hK, hKf, hc, realizes_of_isLEquiv hLA hLB hφ hr⟩

theorem eq_bot_or_eq_of_binaryNaturalSL {n a : ℕ} (hn : 2 ≤ n) {L W Y : Subgroup G}
    [IsMulCommutative ↥W] (hLY : L ≤ Subgroup.normalizer (Y : Set G))
    (hnat : BinaryNaturalSL (autOn L W) ⊤ ⊥ n a) (hYW : Y ≤ W) : Y = ⊥ ∨ Y = W := by
  obtain ⟨K, hK, hKf, -, π, hsurj, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hnat
  by_cases hY : Y = ⊥
  · exact Or.inl hY
  right
  let T : AddSubgroup (Fin n → K) :=
    { carrier := {v | ∃ y : ↥W, (y : G) ∈ Y ∧ β ⟨y, trivial⟩ =
        QuotientGroup.mk ⟨Multiplicative.ofAdd v, trivial⟩}
      add_mem' := by
        rintro v v' ⟨y, hy, hyv⟩ ⟨y', hy', hyv'⟩
        refine ⟨y * y', Y.mul_mem hy hy', ?_⟩
        have e1 : (⟨y * y', trivial⟩ : ↥(⊤ : Subgroup ↥W)) = ⟨y, trivial⟩ * ⟨y', trivial⟩ := rfl
        rw [e1, map_mul, hyv, hyv', ← QuotientGroup.mk_mul]
        rfl
      zero_mem' := by
        refine ⟨1, Y.one_mem, ?_⟩
        have e1 : (⟨1, trivial⟩ : ↥(⊤ : Subgroup ↥W)) = 1 := rfl
        rw [e1, map_one]
        rfl
      neg_mem' := by
        rintro v ⟨y, hy, hyv⟩
        refine ⟨y⁻¹, Y.inv_mem hy, ?_⟩
        have e1 : (⟨y⁻¹, trivial⟩ : ↥(⊤ : Subgroup ↥W)) = (⟨y, trivial⟩)⁻¹ := rfl
        rw [e1, map_inv, hyv, ← QuotientGroup.mk_inv]
        rfl }
  have hTinv : ∀ g : ↥(StatedSL n K), ∀ v ∈ T,
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) ∈ T := by
    rintro g v ⟨y, hy, hyv⟩
    obtain ⟨c, hc, hcg⟩ := Setup.mem_autOn_iff.mp (π g).2
    refine ⟨((π g : ↥(autOn L W)) : MulAut ↥W) y, ?_, hβe g ⟨y, trivial⟩ _ trivial trivial hyv⟩
    rw [← hcg, Setup.coe_conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hLY hc) _).mp hy
  obtain ⟨⟨y₀, hy₀⟩, hy₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hY
  obtain ⟨⟨m₀, _⟩, hm₀⟩ := QuotientGroup.mk_surjective (β ⟨⟨y₀, hYW hy₀⟩, trivial⟩)
  have hv₀T : @Multiplicative.toAdd (Fin n → K) m₀ ∈ T :=
    ⟨⟨y₀, hYW hy₀⟩, hy₀, hm₀.symm⟩
  have hv₀ : @Multiplicative.toAdd (Fin n → K) m₀ ≠ 0 := by
    intro h0
    apply hy₀1
    have hm1 : (m₀ : Multiplicative (Fin n → K)) = 1 :=
      (@Multiplicative.toAdd (Fin n → K)).injective h0
    have hb : β ⟨⟨y₀, hYW hy₀⟩, trivial⟩ = 1 := by
      rw [← hm₀]
      have e2 : (⟨m₀, trivial⟩ : ↥(FFModel.nat (StatedSL n K)).sec) = 1 := Subtype.ext hm1
      rw [e2]
      rfl
    have h2 := (hβk _).mp hb
    rw [Subgroup.mem_bot] at h2
    have h3 : y₀ = 1 := congrArg (fun x : ↥W => (x : G)) h2
    exact Subtype.ext h3
  have hT := eq_top_of_slMulVec_mem hn hTinv hv₀T hv₀
  refine le_antisymm hYW fun w hw => ?_
  obtain ⟨⟨m, _⟩, hm⟩ := QuotientGroup.mk_surjective (β ⟨⟨w, hw⟩, trivial⟩)
  have hmT : @Multiplicative.toAdd (Fin n → K) m ∈ T := by
    rw [hT]
    exact AddSubgroup.mem_top _
  obtain ⟨y, hy, hym⟩ := hmT
  have h1 : β ((⟨y, trivial⟩ : ↥(⊤ : Subgroup ↥W))⁻¹ * ⟨⟨w, hw⟩, trivial⟩) = 1 := by
    rw [map_mul, map_inv, hym, ← hm]
    exact inv_mul_cancel _
  have h2 := (hβk _).mp h1
  rw [Subgroup.mem_bot] at h2
  have h3 : (y : G)⁻¹ * w = 1 := congrArg Subtype.val h2
  have h4 : w = y := by
    rw [inv_mul_eq_one] at h3
    exact h3.symm
  rw [h4]
  exact hy

theorem isNaturalSumUnder_of_le [Finite G] {n : ℕ} (hn : 2 ≤ n) {L V X : Subgroup G}
    (hV : IsNaturalSumUnder n L V) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hXV : X ≤ V)
    (hLX : L ≤ Subgroup.normalizer (X : Set G)) (hX : X ≠ ⊥) : IsNaturalSumUnder n L X := by
  classical
  obtain ⟨k, W, hk, hW, hiso, hind, hsup⟩ := hV
  set i₀ : Fin k := ⟨0, hk⟩ with hi₀
  have hWV : ∀ i, W i ≤ V := fun i => (hW i).1
  have hLW : ∀ i, L ≤ Subgroup.normalizer (W i : Set G) := fun i => (hW i).2.1
  have hirr : ∀ i, ∀ Y : Subgroup G, Y ≤ W i → L ≤ Subgroup.normalizer (Y : Set G) →
      Y = ⊥ ∨ Y = W i := fun i Y hY hLY => by
    obtain ⟨hc, hnat⟩ := (hW i).2.2
    exact eq_bot_or_eq_of_binaryNaturalSL hn hLY hnat hY
  have hWiso : ∀ i, ∃ φ : ↥(W i) ≃* ↥(W i₀), IsLEquiv L φ := fun i =>
    exists_isLEquiv_of_isXSectionIso₂ (hLW i₀) (hiso i i₀)
  have hcore : ∀ m : ℕ, ∀ Y : Subgroup G, Nat.card Y = m → Y ≤ V →
      L ≤ Subgroup.normalizer (Y : Set G) → Y ≠ ⊥ →
      ∃ (k' : ℕ) (U : Fin k' → Subgroup G), 0 < k' ∧
        (∀ j, U j ≤ Y ∧ L ≤ Subgroup.normalizer (U j : Set G) ∧
          ∃ φ : ↥(U j) ≃* ↥(W i₀), IsLEquiv L φ) ∧
        iSupIndep U ∧ ⨆ j, U j = Y := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro Y hYm hYV hLY hY
    have hex : ∃ c, ∃ Y' : Subgroup G, Y' ≤ Y ∧ L ≤ Subgroup.normalizer (Y' : Set G) ∧
        Y' ≠ ⊥ ∧ Nat.card Y' = c := ⟨_, Y, le_rfl, hLY, hY, rfl⟩
    obtain ⟨X₀, hX₀Y, hLX₀, hX₀ne, hX₀c⟩ := Nat.find_spec hex
    have hX₀irr : ∀ Y' : Subgroup G, Y' ≤ X₀ → L ≤ Subgroup.normalizer (Y' : Set G) →
        Y' = ⊥ ∨ Y' = X₀ := by
      intro Y' hY' hLY'
      by_cases h0 : Y' = ⊥
      · exact Or.inl h0
      right
      have h1 := Nat.find_min' hex ⟨Y', hY'.trans hX₀Y, hLY', h0, rfl⟩
      rw [← hX₀c] at h1
      exact Subgroup.eq_of_le_of_card_ge hY' h1
    have hX₀V : X₀ ≤ V := hX₀Y.trans hYV
    obtain ⟨S, hXS, hXS'⟩ := exists_finset_compl hVc hWV hLW hirr hsup hX₀V hLX₀
    set C := ⨆ i ∈ S, W i with hC
    have hCV : C ≤ V := iSup₂_le fun i _ => hWV i
    have hLC : L ≤ Subgroup.normalizer (C : Set G) :=
      le_normalizer_iSup_of_forall fun i => le_normalizer_iSup_of_forall fun _ => hLW i
    obtain ⟨j, hj⟩ : ∃ j, ¬ W j ≤ C := by
      by_contra hall
      push Not at hall
      apply hX₀ne
      have hVC : V ≤ C := hsup ▸ iSup_le hall
      rw [eq_bot_iff, ← hXS]
      exact le_inf le_rfl (hX₀V.trans hVC)
    have hjS : j ∉ S := fun hjS =>
      hj (le_iSup₂_of_le (f := fun i (_ : i ∈ S) => W i) j hjS le_rfl)
    have hjC : W j ⊓ C = ⊥ := by
      have := hind.disjoint_biSup (y := (S : Set (Fin k))) (x := j) (by simpa using hjS)
      rw [disjoint_iff] at this
      simpa using this
    obtain ⟨p, hp⟩ := exists_proj_of_compl hVc hX₀V hCV (hWV j) hXS hXS'
    have hpinj : Function.Injective p := by
      rw [injective_iff_map_eq_one]
      intro w hw
      have h1 := hp w
      rw [hw] at h1
      simp only [OneMemClass.coe_one, inv_one, one_mul] at h1
      have : (w : G) ∈ W j ⊓ C := ⟨w.2, h1⟩
      rw [hjC, Subgroup.mem_bot] at this
      exact Subtype.ext this
    have hpL : ∀ l ∈ L, ∀ w w' : ↥(W j), (w' : G) = l * w * l⁻¹ →
        ((p w' : ↥X₀) : G) = l * (p w : G) * l⁻¹ := by
      intro l hl w w' hw'
      refine eq_of_inv_mul_mem hXS (p w').2
        ((Subgroup.mem_normalizer_iff.mp (hLX₀ hl) _).mp (p w).2) (hp w') ?_
      have e : (l * (p w : G) * l⁻¹)⁻¹ * w' = l * ((p w : G)⁻¹ * w) * l⁻¹ := by
        rw [hw']
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hLC hl) _).mp (hp w)
    have hpsurj : Function.Surjective p := by
      set R := p.range.map X₀.subtype with hR
      have hRX : R ≤ X₀ := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hLR : L ≤ Subgroup.normalizer (R : Set G) := fun l hl =>
        A4.mem_normalizer_of_conj_mem fun x hx => by
          obtain ⟨x', ⟨w, rfl⟩, rfl⟩ := hx
          have hw' : l * (w : G) * l⁻¹ ∈ W j :=
            (Subgroup.mem_normalizer_iff.mp (hLW j hl) _).mp w.2
          exact ⟨p ⟨_, hw'⟩, ⟨_, rfl⟩, hpL l hl w ⟨_, hw'⟩ rfl⟩
      rcases hX₀irr R hRX hLR with h0 | h1
      · exfalso
        have hWj1 : W j ≠ ⊥ := fun h => hj (h ▸ bot_le)
        obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWj1
        apply hw1
        apply hpinj
        rw [map_one]
        have : ((p w : ↥X₀) : G) ∈ R := ⟨p w, ⟨w, rfl⟩, rfl⟩
        rw [h0, Subgroup.mem_bot] at this
        exact Subtype.ext this
      · intro x
        have : (x : G) ∈ R := by
          rw [h1]
          exact x.2
        obtain ⟨x', ⟨w, rfl⟩, hx'⟩ := this
        exact ⟨w, Subtype.ext hx'⟩
    set φj : ↥(W j) ≃* ↥X₀ := MulEquiv.ofBijective p ⟨hpinj, hpsurj⟩ with hφj
    have hφjL : IsLEquiv L φj := fun l hl w w' hw' => hpL l hl w w' hw'
    obtain ⟨ψj, hψj⟩ := hWiso j
    have hX₀iso : ∃ φ : ↥X₀ ≃* ↥(W i₀), IsLEquiv L φ :=
      ⟨φj.symm.trans ψj, (hφjL.symm (hLW j)).trans hψj⟩
    set X₁ := Y ⊓ C with hX₁
    have hLX₁ : L ≤ Subgroup.normalizer (X₁ : Set G) := fun l hl =>
      A4.mem_normalizer_inf (hLY hl) (hLC hl)
    have hX₀X₁ : X₀ ⊓ X₁ = ⊥ := le_bot_iff.mp ((inf_le_inf_left _ inf_le_right).trans hXS.le)
    have hYsup : X₀ ⊔ X₁ = Y := by
      refine le_antisymm (_root_.sup_le hX₀Y inf_le_left) fun y hy => ?_
      have hy' : y ∈ X₀ ⊔ C := by
        rw [hXS']
        exact hYV hy
      obtain ⟨x, hx, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_comm hVc hX₀V hCV hy'
      have hcY : c ∈ Y := by
        have := Y.mul_mem (Y.inv_mem (hX₀Y hx)) hy
        simpa using this
      exact Subgroup.mul_mem_sup hx ⟨hcY, hc⟩
    by_cases hX₁0 : X₁ = ⊥
    · refine ⟨1, fun _ => X₀, Nat.one_pos, fun _ => ⟨hX₀Y, hLX₀, hX₀iso⟩, ?_, ?_⟩
      · refine iSupIndep_def.mpr fun i => ?_
        have h0 : (⨆ (j : Fin 1) (_ : j ≠ i), (fun _ : Fin 1 => X₀) j) = ⊥ :=
          le_bot_iff.mp (iSup₂_le fun j hj => absurd (Subsingleton.elim j i) hj)
        rw [h0]
        exact disjoint_bot_right
      · rw [iSup_const, ← hYsup, hX₁0, sup_bot_eq]
    · have hX₁lt : Nat.card X₁ < m := by
        rw [← hYm]
        refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h => hX₀ne ?_)
        rw [← hX₀X₁, h, inf_eq_left.mpr hX₀Y]
      obtain ⟨k₁, U₁, -, hU₁, hU₁ind, hU₁sup⟩ :=
        ih _ hX₁lt X₁ rfl (inf_le_left.trans hYV) hLX₁ hX₁0
      have hU₁X₁ : ∀ i, U₁ i ≤ X₁ := fun i => hU₁sup ▸ le_iSup U₁ i
      refine ⟨k₁ + 1, Fin.cons X₀ U₁, Nat.succ_pos _, ?_, ?_, ?_⟩
      · intro i
        cases i using Fin.cases with
        | zero => exact ⟨hX₀Y, hLX₀, hX₀iso⟩
        | succ i =>
          simp only [Fin.cons_succ]
          exact ⟨(hU₁X₁ i).trans inf_le_left, (hU₁ i).2.1, (hU₁ i).2.2⟩
      · rw [iSupIndep_def]
        intro i
        cases i using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero]
          refine (disjoint_iff.mpr hX₀X₁).mono_right (iSup₂_le fun j hj => ?_)
          obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
          simp only [Fin.cons_succ]
          exact hU₁X₁ j'
        | succ i =>
          simp only [Fin.cons_succ]
          set B := ⨆ (j' : Fin k₁) (_ : j' ≠ i), U₁ j' with hB
          have hBX₁ : B ≤ X₁ := iSup₂_le fun j' _ => hU₁X₁ j'
          have hle : (⨆ (j : Fin (k₁ + 1)) (_ : j ≠ i.succ),
              (Fin.cons X₀ U₁ : Fin (k₁ + 1) → Subgroup G) j) ≤ X₀ ⊔ B := by
            refine iSup₂_le fun j hj => ?_
            cases j using Fin.cases with
            | zero =>
              simp only [Fin.cons_zero]
              exact le_sup_left
            | succ j' =>
              simp only [Fin.cons_succ]
              have hj' : j' ≠ i := fun h => hj (h ▸ rfl)
              exact (le_iSup₂_of_le (f := fun j' (_ : j' ≠ i) => U₁ j') j' hj' le_rfl).trans
                le_sup_right
          refine Disjoint.mono_right hle (disjoint_iff.mpr ?_)
          exact inf_sup_eq_bot_of_comm hVc hX₀V (hBX₁.trans (inf_le_left.trans hYV))
            (disjoint_iff.mp ((iSupIndep_def.mp hU₁ind) i))
            (le_bot_iff.mp ((inf_le_inf_left _ (_root_.sup_le (hU₁X₁ i) hBX₁)).trans hX₀X₁.le))
      · apply le_antisymm
        · refine iSup_le fun i => ?_
          cases i using Fin.cases with
          | zero =>
            simp only [Fin.cons_zero]
            exact hX₀Y
          | succ i =>
            simp only [Fin.cons_succ]
            exact (hU₁X₁ i).trans inf_le_left
        · rw [← hYsup, ← hU₁sup]
          refine _root_.sup_le (le_iSup_of_le 0 (by simp)) (iSup_le fun i => ?_)
          exact le_iSup_of_le i.succ (by simp)
  obtain ⟨k', U, hk', hU, hUind, hUsup⟩ := hcore _ X rfl hXV hLX hX
  have hUc : ∀ j, IsMulCommutative ↥(U j) := fun j =>
    ⟨⟨fun x y => Subtype.ext (hVc _ ((hU j).1.trans hXV x.2) _ ((hU j).1.trans hXV y.2))⟩⟩
  refine ⟨k', U, hk', fun j => ⟨(hU j).1, (hU j).2.1, hUc j, ?_⟩, fun i j => ?_, hUind, hUsup⟩
  · obtain ⟨φ, hφ⟩ := (hU j).2.2
    obtain ⟨hc₀, hnat₀⟩ := (hW i₀).2.2
    have := hUc j
    exact binaryNaturalSL_of_isLEquiv (hLW i₀) (hU j).2.1 (hφ.symm (hU j).2.1) hnat₀
  · obtain ⟨φi, hφi⟩ := (hU i).2.2
    obtain ⟨φj, hφj⟩ := (hU j).2.2
    exact isXSectionIso₂_of_isLEquiv (hφi.trans (hφj.symm (hU j).2.1))

end CFSG.Quasithin.H13.Ch4
