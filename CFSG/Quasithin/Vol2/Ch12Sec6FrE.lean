module

public import CFSG.Quasithin.Vol2.Ch12Sec6L1c

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126L1c Equiv
open scoped IsMulCommutative

namespace S126FE

theorem mem_zpowers_allOnes {x : PermMod 8} (h : x ∈ Subgroup.zpowers (allOnes 8)) :
    x = 1 ∨ x = allOnes 8 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  have h2 : (allOnes 8 : PermMod 8) ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    decide
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [_root_.zpow_mul, h2, _root_.one_zpow]
  · right
    rw [_root_.zpow_add, _root_.zpow_mul, h2, _root_.one_zpow, one_mul, zpow_one]

@[expose] def eOm : ↥(coreMod 8) := ⟨allOnes 8, allOnes_mem⟩

theorem eOm_ne_one : eOm ≠ 1 := by
  intro h
  have h1 := congrArg (fun m : ↥(coreMod 8) =>
    (Multiplicative.toAdd (m : PermMod 8) : Fin 8 → ZMod 2) 0) h
  exact absurd h1 (by decide)

theorem eOm_mul_self : eOm * eOm = 1 := by
  apply Subtype.ext
  decide

theorem coreAct_eOm (σ : Perm (Fin 8)) : coreAct 8 σ eOm = eOm :=
  Subtype.ext (by rw [coreAct_coe]; exact S126.permAct_allOnes σ)

theorem fix_A8_eq {m : ↥(coreMod 8)}
    (h : ∀ σ ∈ alternatingGroup (Fin 8), coreAct 8 σ m = m) : m = 1 ∨ m = eOm := by
  rcases eq_of_fix_Q8 (fun σ hσ => h σ hσ.2) with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Subtype.ext h1)

theorem mem_Ker8 {m : ↥(coreMod 8)} (h : m ∈ B5FinS8.Ker8) : m = 1 ∨ m = eOm := by
  have h' : (m : PermMod 8) ∈ Subgroup.zpowers (allOnes 8) := (Subgroup.mem_subgroupOf.1 h).1
  rcases mem_zpowers_allOnes h' with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

theorem eOm_mem_Ker8 : eOm ∈ B5FinS8.Ker8 :=
  Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_zpowers _, allOnes_mem⟩

theorem mk_eq_one_iff (m : ↥(coreMod 8)) : (QuotientGroup.mk m : D8) = 1 ↔ m = 1 ∨ m = eOm := by
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro h
    rcases mem_zpowers_allOnes (h : (m : PermMod 8) ∈ Subgroup.zpowers (allOnes 8)) with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact (Subgroup.mem_zpowers (allOnes 8) : allOnes 8 ∈ Subgroup.zpowers (allOnes 8))

theorem k8E (μ : ↥(coreMod 8) →* ↥(coreMod 8)) (hinj : Function.Injective μ)
    (hcomm : ∀ σ ∈ alternatingGroup (Fin 8), ∀ m, μ (coreAct 8 σ m) = coreAct 8 σ (μ m)) :
    ∀ m, μ m = m := by
  have he : μ eOm = eOm := by
    rcases fix_A8_eq (m := μ eOm) (fun σ hσ => by rw [← hcomm σ hσ, coreAct_eOm]) with h | h
    · exact absurd (hinj (h.trans (map_one μ).symm)) eOm_ne_one
    · exact h
  have hK : B5FinS8.Ker8 ≤ B5FinS8.Ker8.comap μ := by
    intro m hm
    rw [Subgroup.mem_comap]
    rcases mem_Ker8 hm with rfl | rfl
    · rw [map_one]
      exact Subgroup.one_mem _
    · rw [he]
      exact eOm_mem_Ker8
  let μb : B5FinS8.Mod8 →* B5FinS8.Mod8 := QuotientGroup.map _ _ μ hK
  have hμb : ∀ m, μb (QuotientGroup.mk m) = QuotientGroup.mk (μ m) := fun _ => rfl
  have hinjb : Function.Injective μb := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hμb, QuotientGroup.eq_one_iff] at hq
    rw [QuotientGroup.eq_one_iff]
    rcases mem_Ker8 hq with h | h
    · rw [hinj (h.trans (map_one μ).symm)]
      exact Subgroup.one_mem _
    · rw [hinj (h.trans he.symm)]
      exact eOm_mem_Ker8
  have hcb : ∀ σ ∈ alternatingGroup (Fin 8), ∀ q,
      μb (B5FinS8.act8 σ q) = B5FinS8.act8 σ (μb q) := by
    intro σ hσ q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    rw [B5FinS8.act8_mk, hμb, hμb, B5FinS8.act8_mk]
    congr 1
    exact hcomm σ hσ m
  have hk := B5FinS8.k8 μb hinjb hcb
  have hmod : ∀ m, μ m * m⁻¹ = 1 ∨ μ m * m⁻¹ = eOm := by
    intro m
    have h1 := hk (QuotientGroup.mk m)
    rw [hμb, QuotientGroup.eq] at h1
    have e : μ m * m⁻¹ = ((μ m)⁻¹ * m)⁻¹ := by rw [mul_inv_rev, inv_inv, mul_comm]
    rcases mem_Ker8 h1 with h | h
    · left
      rw [e, h, inv_one]
    · right
      rw [e, h, inv_eq_of_mul_eq_one_right eOm_mul_self]
  let δ : ↥(coreMod 8) →* ↥(coreMod 8) :=
    { toFun := fun m => μ m * m⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hδσ : ∀ σ ∈ alternatingGroup (Fin 8), ∀ m, δ (coreAct 8 σ m) = δ m := by
    intro σ hσ m
    change μ (coreAct 8 σ m) * (coreAct 8 σ m)⁻¹ = μ m * m⁻¹
    rw [hcomm σ hσ, ← map_inv, ← map_mul]
    rcases hmod m with h | h
    · rw [h, map_one]
    · rw [h, coreAct_eOm]
  have hδ1 : ∀ m, δ m = 1 := by
    intro m
    induction VolI.coreMod_eight_gen m using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨σ, y, rfl⟩ := hx
      rw [map_mul, map_inv, show VolI.act8 σ y = coreAct 8 σ y from rfl, hδσ σ σ.2,
        mul_inv_cancel]
    | one => exact map_one δ
    | mul x y _ _ hx hy => rw [map_mul, hx, hy, one_mul]
    | inv x _ hx => rw [map_inv, hx, inv_one]
  intro m
  exact mul_inv_eq_one.1 (hδ1 m)

variable {G : Type} [Group G] {T L V : Subgroup G} [IsMulCommutative ↥V]

structure Frame126E (F : Frame126 T L V) where
  γ : ↥V ≃* ↥(coreMod 8)
  β_eq : ∀ v : ↥V, F.β v = QuotientGroup.mk (γ v)
  equi : ∀ (σ : ↥(alternatingGroup (Fin 8))) (v : ↥V),
    γ (((F.π σ : ↥(autOn L V)) : MulAut ↥V) v) = coreAct 8 σ (γ v)
  act : ∀ x : G, x ∈ Subgroup.normalizer (L : Set G) → x ∈ Subgroup.normalizer (V : Set G) →
    ∀ σ : Perm (Fin 8), ActsAs F x σ → ∀ v w : ↥V, (w : G) = x * v * x⁻¹ →
      γ w = coreAct 8 σ (γ v)

omit [IsMulCommutative ↥V] in
theorem conj_mem_L {x l : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) (hl : l ∈ L) :
    x * l * x⁻¹ ∈ L :=
  (Subgroup.mem_normalizer_iff.1 hx l).1 hl

theorem eq_of_dAct (F : Frame126 T L V) {a b : ↥(autOn L V)}
    (h : ∀ v : ↥V, F.β ((a : MulAut ↥V) v) = F.β ((b : MulAut ↥V) v)) : a = b := by
  obtain ⟨σ, rfl⟩ := F.π_surj a
  obtain ⟨τ, rfl⟩ := F.π_surj b
  have h1 : ∀ y : D8, dAct (σ : Perm (Fin 8)) y = dAct (τ : Perm (Fin 8)) y := by
    intro y
    obtain ⟨v, rfl⟩ := F.β_surj y
    rw [← F.equi, ← F.equi]
    exact h v
  have h2 : ∀ y : D8, dAct ((τ : Perm (Fin 8))⁻¹ * σ) y = y := by
    intro y
    rw [dAct_mul, h1, dAct_inv_dAct]
  have h3 := eq_one_of_dAct h2
  rw [inv_mul_eq_one] at h3
  have h4 : σ = τ := Subtype.ext h3.symm
  rw [h4]

theorem conj_pi (F : Frame126 T L V) {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) {σ : Perm (Fin 8)} (hx : ActsAs F x σ)
    (τ : ↥(alternatingGroup (Fin 8))) (hστ : σ * τ * σ⁻¹ ∈ alternatingGroup (Fin 8))
    (v : ↥V) :
    conjAct V ⟨x, hxV⟩ (((F.π τ : ↥(autOn L V)) : MulAut ↥V) v) =
      ((F.π ⟨σ * τ * σ⁻¹, hστ⟩ : ↥(autOn L V)) : MulAut ↥V) (conjAct V ⟨x, hxV⟩ v) := by
  set a : MulAut ↥V := conjAct V ⟨x, hxV⟩ with ha
  obtain ⟨l, hl, hlL, hla⟩ := mem_autOn_iff_exists.mp (F.π τ).2
  have hxl : x * l * x⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hxV hl) (Subgroup.inv_mem _ hxV)
  have hb : conjAct V ⟨x * l * x⁻¹, hxl⟩ ∈ autOn L V :=
    mem_autOn_iff_exists.mpr ⟨_, hxl, conj_mem_L hxL hlL, rfl⟩
  have hbe : ∀ u : ↥V, conjAct V ⟨x * l * x⁻¹, hxl⟩ u = a ((conjAct V ⟨l, hl⟩) (a⁻¹ u)) := by
    intro u
    apply Subtype.ext
    have e1 : ((a⁻¹ u : ↥V) : G) = x⁻¹ * u * x := by
      have : a (a⁻¹ u) = u := by simp
      have h2 : ((a (a⁻¹ u) : ↥V) : G) = x * (a⁻¹ u : ↥V) * x⁻¹ := rfl
      rw [this] at h2
      calc ((a⁻¹ u : ↥V) : G) = x⁻¹ * (x * (a⁻¹ u : ↥V) * x⁻¹) * x := by group
        _ = x⁻¹ * u * x := by rw [← h2]
    change x * l * x⁻¹ * u * (x * l * x⁻¹)⁻¹ = x * (l * ((a⁻¹ u : ↥V) : G) * l⁻¹) * x⁻¹
    rw [e1]
    group
  have key : (⟨_, hb⟩ : ↥(autOn L V)) = F.π ⟨σ * τ * σ⁻¹, hστ⟩ := by
    apply eq_of_dAct F
    intro u
    change F.β (conjAct V ⟨x * l * x⁻¹, hxl⟩ u) = _
    rw [hbe, F.equi]
    have hxu : ActsAs F x σ := hx
    have h1 : F.β (a ((conjAct V ⟨l, hl⟩) (a⁻¹ u))) =
        dAct σ (F.β ((conjAct V ⟨l, hl⟩) (a⁻¹ u))) := hxu _ _ rfl
    rw [h1, hla, F.equi]
    have h2 : F.β (a⁻¹ u) = dAct σ⁻¹ (F.β u) := by
      have h3 : F.β u = dAct σ (F.β (a⁻¹ u)) := hxu (a⁻¹ u) u (by
        have h4 : ((a (a⁻¹ u) : ↥V) : G) = x * ((a⁻¹ u : ↥V) : G) * x⁻¹ := rfl
        rwa [show a (a⁻¹ u) = u by simp] at h4)
      rw [h3, dAct_inv_dAct]
    rw [h2, ← dAct_mul, ← dAct_mul]
  have h5 := congrArg (fun c : ↥(autOn L V) => ((c : MulAut ↥V) (a v))) key
  simp only at h5
  rw [← h5, hbe, hla]
  congr 1
  simp

theorem exists_gamma [Finite G] (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    ∃ γ : ↥V ≃* ↥(coreMod 8), ∀ (σ : ↥(alternatingGroup (Fin 8))) (v : ↥V),
      γ (((F.π σ : ↥(autOn L V)) : MulAut ↥V) v) = coreAct 8 σ (γ v) := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hVL : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hVe : IsElemAbelian 2 V := isElemAbelian_of_reduced (hVT.trans le_sup_right) hred
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hVe.2 v v.2)
  obtain ⟨hc, hmod⟩ := hH.module
  set Z : Subgroup ↥V := (Subgroup.centralizer (L : Set G)).subgroupOf V with hZdef
  have hZfix : Z ≤ fixV (autOn L V) := InternalSec.le_fixV_autOn inf_le_right
  have hcomm : commV (autOn L V) = ⊤ := InternalSec.commV_autOn_eq_top hLV hVL
  have hU : XMod.commOf ↥(autOn L V) (⊤ : Subgroup ↥V) = ⊤ := by
    rw [commOf_top_eq, hcomm]
  have hZ1 : Z ≠ ⊥ := by
    intro h
    apply hZ
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥V) ∈ Z := hx.2
    rw [h, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  obtain ⟨π', Φ, hπ's, hΦ⟩ := A7.LinCover.exists_mulEquiv_coreMod_eight hV2 hmod hZfix hU hZ1
  let Φ' : ↥V ≃* ↥(coreMod 8) := Subgroup.topEquiv.symm.trans Φ
  have hΦ' : ∀ (τ : ↥(alternatingGroup (Fin 8))) (v : ↥V),
      Φ' (((π' τ : ↥(autOn L V)) : MulAut ↥V) v) = coreAct 8 τ (Φ' v) := fun τ v =>
    hΦ τ ⟨v, Subgroup.mem_top v⟩ (Subgroup.mem_top _)
  have hcardA := card_autOn hH hLV
  obtain ⟨e⟩ := Finite.card_eq.1 hcardA.symm
  have hπ'b : Function.Bijective π' := ⟨(Finite.injective_iff_surjective_of_equiv e).2 hπ's, hπ's⟩
  have hπb : Function.Bijective F.π :=
    ⟨(Finite.injective_iff_surjective_of_equiv e).2 F.π_surj, F.π_surj⟩
  let α : ↥(alternatingGroup (Fin 8)) ≃* ↥(alternatingGroup (Fin 8)) :=
    (MulEquiv.ofBijective F.π hπb).trans (MulEquiv.ofBijective π' hπ'b).symm
  have hα : ∀ σ, π' (α σ) = F.π σ := fun σ =>
    (MulEquiv.ofBijective π' hπ'b).apply_symm_apply (F.π σ)
  set g : Perm (Fin 8) := CFSG.QuasithinUnique.Claim2526.conjEquiv8.symm α with hgdef
  have hg : ∀ σ : ↥(alternatingGroup (Fin 8)), ((α σ : ↥(alternatingGroup (Fin 8))) :
      Perm (Fin 8)) = g * σ * g⁻¹ := by
    intro σ
    have h1 : MulAut.conjNormal g = α :=
      CFSG.QuasithinUnique.Claim2526.conjEquiv8.apply_symm_apply α
    rw [← h1, MulAut.conjNormal_apply]
  refine ⟨Φ'.trans (coreAct 8 g⁻¹), fun σ v => ?_⟩
  change coreAct 8 g⁻¹ (Φ' _) = coreAct 8 σ (coreAct 8 g⁻¹ (Φ' v))
  rw [← hα σ, hΦ', hg σ, ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
  congr 2
  group

theorem beta_eq_of_gamma (F : Frame126 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (γ : ↥V ≃* ↥(coreMod 8)) (hγ : ∀ (σ : ↥(alternatingGroup (Fin 8))) (v : ↥V),
      γ (((F.π σ : ↥(autOn L V)) : MulAut ↥V) v) = coreAct 8 σ (γ v)) :
    ∀ v : ↥V, F.β v = QuotientGroup.mk (γ v) := by
  have hπfix : ∀ (σ : ↥(alternatingGroup (Fin 8))) (v : ↥V),
      (v : G) ∈ Subgroup.centralizer (L : Set G) →
        ((F.π σ : ↥(autOn L V)) : MulAut ↥V) v = v := by
    intro σ v hv
    obtain ⟨l, hl, hlL, hla⟩ := mem_autOn_iff_exists.mp (F.π σ).2
    rw [← hla]
    apply Subtype.ext
    change l * v * l⁻¹ = v
    rw [Subgroup.mem_centralizer_iff.1 hv l hlL, mul_inv_cancel_right]
  have ha : ∀ v : ↥V, F.β v = 1 → γ v = 1 ∨ γ v = eOm := by
    intro v hv
    have hvL := (F.β_ker v).1 hv
    exact fix_A8_eq fun σ hσ => by
      rw [← hγ ⟨σ, hσ⟩ v, hπfix ⟨σ, hσ⟩ v hvL]
  have hb : ∀ v : ↥V, (γ v = 1 ∨ γ v = eOm) → F.β v = 1 := by
    intro v hv
    rw [F.β_ker]
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hfix : ∀ σ, ((F.π σ : ↥(autOn L V)) : MulAut ↥V) v = v := by
      intro σ
      apply γ.injective
      rw [hγ]
      rcases hv with h | h
      · rw [h, map_one]
      · rw [h, coreAct_eOm]
    obtain ⟨σ, hσ⟩ := F.π_surj ⟨conjAct V ⟨l, hLV hl⟩,
      mem_autOn_iff_exists.mpr ⟨l, hLV hl, hl, rfl⟩⟩
    have h1 := hfix σ
    rw [hσ] at h1
    have h2 : l * v * l⁻¹ = v := congrArg Subtype.val h1
    calc l * v = l * v * l⁻¹ * l := by group
      _ = v * l := by rw [h2]
  let f : ↥V →* D8 := (QuotientGroup.mk' (natKer 8)).comp γ.toMonoidHom
  have hker : F.β.ker ≤ f.ker := by
    intro v hv
    rw [MonoidHom.mem_ker] at hv ⊢
    change (QuotientGroup.mk (γ v) : D8) = 1
    exact (mk_eq_one_iff _).2 (ha v hv)
  let eβ := QuotientGroup.quotientKerEquivOfSurjective F.β F.β_surj
  let μ : D8 →* D8 := (QuotientGroup.lift F.β.ker f hker).comp eβ.symm.toMonoidHom
  have hμ : ∀ v, μ (F.β v) = QuotientGroup.mk (γ v) := by
    intro v
    have h1 : eβ.symm (F.β v) = QuotientGroup.mk v := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift F.β.ker f hker (eβ.symm (F.β v)) = _
    rw [h1, QuotientGroup.lift_mk]
    rfl
  have hμi : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨v, rfl⟩ := F.β_surj y
    rw [hμ, mk_eq_one_iff] at hy
    exact hb v hy
  have hμc : ∀ σ : ↥(alternatingGroup (Fin 8)), ∀ y, μ (dAct σ y) = dAct σ (μ y) := by
    intro σ y
    obtain ⟨v, rfl⟩ := F.β_surj y
    rw [← F.equi, hμ, hμ, hγ, dAct_mk]
  let μ' : B5FinS8.Mod8 →* B5FinS8.Mod8 :=
    S126Ex.e8.symm.toMonoidHom.comp (μ.comp S126Ex.e8.toMonoidHom)
  have hμ'i : Function.Injective μ' :=
    S126Ex.e8.symm.injective.comp (hμi.comp S126Ex.e8.injective)
  have he8 : ∀ (σ : Perm (Fin 8)) (y : D8),
      S126Ex.e8.symm (dAct σ y) = B5FinS8.act8 σ (S126Ex.e8.symm y) := by
    intro σ y
    rw [MulEquiv.symm_apply_eq, S126Ex.e8_act, MulEquiv.apply_symm_apply]
  have hμ'c : ∀ σ ∈ alternatingGroup (Fin 8), ∀ q,
      μ' (B5FinS8.act8 σ q) = B5FinS8.act8 σ (μ' q) := by
    intro σ hσ q
    change S126Ex.e8.symm (μ (S126Ex.e8 (B5FinS8.act8 σ q))) =
      B5FinS8.act8 σ (S126Ex.e8.symm (μ (S126Ex.e8 q)))
    rw [S126Ex.e8_act, ← he8]
    congr 1
    exact hμc ⟨σ, hσ⟩ _
  have hk := B5FinS8.k8 μ' hμ'i hμ'c
  intro v
  rw [← hμ v]
  have h1 := hk (S126Ex.e8.symm (F.β v))
  change S126Ex.e8.symm (μ (S126Ex.e8 (S126Ex.e8.symm (F.β v)))) = _ at h1
  rw [MulEquiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq] at h1
  exact h1.symm

theorem act_of_gamma (F : Frame126 T L V) (γ : ↥V ≃* ↥(coreMod 8))
    (hγ : ∀ (σ : ↥(alternatingGroup (Fin 8))) (v : ↥V),
      γ (((F.π σ : ↥(autOn L V)) : MulAut ↥V) v) = coreAct 8 σ (γ v)) {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxV : x ∈ Subgroup.normalizer (V : Set G))
    {σ : Perm (Fin 8)} (hx : ActsAs F x σ) :
    ∀ v w : ↥V, (w : G) = x * v * x⁻¹ → γ w = coreAct 8 σ (γ v) := by
  set a : MulAut ↥V := conjAct V ⟨x, hxV⟩ with ha
  have hxa : ∀ v : ↥V, ((a v : ↥V) : G) = x * v * x⁻¹ := fun v => rfl
  let κ : ↥(coreMod 8) →* ↥(coreMod 8) :=
    (coreAct 8 σ⁻¹).toMonoidHom.comp (γ.toMonoidHom.comp (a.toMonoidHom.comp γ.symm.toMonoidHom))
  have hκ : ∀ v : ↥V, κ (γ v) = coreAct 8 σ⁻¹ (γ (a v)) := by
    intro v
    change coreAct 8 σ⁻¹ (γ (a (γ.symm (γ v)))) = _
    rw [MulEquiv.symm_apply_apply]
  have hσA : ∀ τ : ↥(alternatingGroup (Fin 8)), σ * τ * σ⁻¹ ∈ alternatingGroup (Fin 8) := by
    intro τ
    have hn : (alternatingGroup (Fin 8)).Normal := inferInstance
    exact hn.conj_mem _ τ.2 σ
  have hκi : Function.Injective κ := by
    intro m₁ m₂ h
    obtain ⟨v₁, rfl⟩ := γ.surjective m₁
    obtain ⟨v₂, rfl⟩ := γ.surjective m₂
    rw [hκ, hκ] at h
    have h1 := (coreAct 8 σ⁻¹).injective h
    rw [a.injective (γ.injective h1)]
  have hκc : ∀ τ ∈ alternatingGroup (Fin 8), ∀ m, κ (coreAct 8 τ m) = coreAct 8 τ (κ m) := by
    intro τ hτ m
    obtain ⟨v, rfl⟩ := γ.surjective m
    rw [← hγ ⟨τ, hτ⟩ v, hκ, hκ]
    have h1 := conj_pi F hxL hxV hx ⟨τ, hτ⟩ (hσA ⟨τ, hτ⟩) v
    rw [← ha] at h1
    rw [h1, hγ, ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    change σ⁻¹ * (σ * τ * σ⁻¹) = τ * σ⁻¹
    group
  have hκ1 := k8E κ hκi hκc
  intro v w hw
  have hwa : w = a v := Subtype.ext hw
  have h1 := hκ1 (γ v)
  rw [hκ, ← hwa] at h1
  have h2 := congrArg (coreAct 8 σ) h1
  rwa [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h2

theorem exists_frame126E [Finite G] (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    Nonempty (Frame126E F) := by
  obtain ⟨γ, hγ⟩ := exists_gamma h1222 F hH hZ
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hβ := beta_eq_of_gamma F hLV γ hγ
  exact ⟨⟨γ, hβ, hγ, fun x hxL hxV σ hx => act_of_gamma F γ hγ hxL hxV hx⟩⟩

end S126FE

end CFSG.Quasithin.H13
