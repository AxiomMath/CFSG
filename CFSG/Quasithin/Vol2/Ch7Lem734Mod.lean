module

public import CFSG.Quasithin.Vol2.Ch7Lem734Loc
public import CFSG.Quasithin.Vol2.Ch7Fano
public import CFSG.Quasithin.Vol2.Ch7OrthFF
public import CFSG.Quasithin.Background.InternalSecIso

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section Group

variable {G : Type} [Group G]

private theorem conj_mem_commutator {A B : Subgroup G} {t : G}
    (hA : t ∈ Subgroup.normalizer (A : Set G)) (hB : t ∈ Subgroup.normalizer (B : Set G))
    {x : G} (hx : x ∈ ⁅A, B⁆) : t * x * t⁻¹ ∈ ⁅A, B⁆ := by
  rw [Subgroup.commutator_def] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    apply Subgroup.subset_closure
    refine ⟨t * a * t⁻¹, (Subgroup.mem_normalizer_iff.mp hA a).mp ha, t * b * t⁻¹,
      (Subgroup.mem_normalizer_iff.mp hB b).mp hb, ?_⟩
    simp only [commutatorElement_def]
    group
  | one => simp
  | mul y z _ _ hy hz =>
    have e : t * (y * z) * t⁻¹ = (t * y * t⁻¹) * (t * z * t⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
    have e : t * y⁻¹ * t⁻¹ = (t * y * t⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hy

private theorem mem_normalizer_conjClosure {Z H : Subgroup G} {t : G}
    (hZ : t ∈ Subgroup.normalizer (Z : Set G)) (hH : t ∈ Subgroup.normalizer (H : Set G)) :
    t ∈ Subgroup.normalizer (conjClosure Z H : Set G) := by
  have key : ∀ s : G, s ∈ Subgroup.normalizer (Z : Set G) →
      s ∈ Subgroup.normalizer (H : Set G) →
        ∀ x ∈ conjClosure Z H, s * x * s⁻¹ ∈ conjClosure Z H := by
    intro s hsZ hsH x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hy
      have e : s * (h * z * h⁻¹) * s⁻¹ = (s * h * s⁻¹) * (s * z * s⁻¹) * (s * h * s⁻¹)⁻¹ := by
        group
      rw [e]
      exact mem_conjClosure ((Subgroup.mem_normalizer_iff.mp hsH h).mp hh)
        ((Subgroup.mem_normalizer_iff.mp hsZ z).mp hz)
    | one => simp
    | mul y z _ _ hy hz =>
      have e : s * (y * z) * s⁻¹ = (s * y * s⁻¹) * (s * z * s⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hy hz
    | inv y _ hy =>
      have e : s * y⁻¹ * s⁻¹ = (s * y * s⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key t hZ hH x, fun hx => ?_⟩
  have := key t⁻¹ (Subgroup.inv_mem _ hZ) (Subgroup.inv_mem _ hH) _ hx
  simpa [mul_assoc] using this

private theorem card_conjugate (H : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate H g) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

private theorem mem_conjugate_iff_conj {K : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate K g ↔ g * x * g⁻¹ ∈ K := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

private theorem conjugate_mono {J K : Subgroup G} (h : J ≤ K) (g : G) :
    CFSG.conjugate J g ≤ CFSG.conjugate K g :=
  Subgroup.map_mono h

private theorem conjugate_conjugate_inv' (K : Subgroup G) (g : G) :
    CFSG.conjugate (CFSG.conjugate K g) g⁻¹ = K := by
  ext x
  rw [mem_conjugate_iff_conj, mem_conjugate_iff_conj]
  constructor
  · intro h
    simpa [mul_assoc] using h
  · intro h
    simpa [mul_assoc] using h

private theorem conjugate_eq_of_mem_normalizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : CFSG.conjugate K g = K := by
  ext x
  rw [mem_conjugate_iff_conj]
  exact (Subgroup.mem_normalizer_iff.mp hg x).symm

private theorem le_normalizer_conjugate {X J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hXJ : X ≤ Subgroup.normalizer (J : Set G)) :
    X ≤ Subgroup.normalizer (CFSG.conjugate J g : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_conjugate_iff_conj, mem_conjugate_iff_conj]
  have hgl : g * l * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hg l).mp hl
  have e : g * (l * x * l⁻¹) * g⁻¹ = (g * l * g⁻¹) * (g * x * g⁻¹) * (g * l * g⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp (hXJ hgl) _

private theorem le_normalizer_inf {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hA hl) x,
    Subgroup.mem_normalizer_iff.mp (hB hl) x]

private theorem inf_subgroupOf_eq_bot_of {A B V : Subgroup G} (h : A ⊓ B = ⊥) :
    A.subgroupOf V ⊓ B.subgroupOf V = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : (x : G) ∈ A ⊓ B := Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
    (Subgroup.mem_inf.mp hx).2⟩
  rw [h, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.mpr (Subtype.ext hx')

end Group

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem commutator_fsuV_fsuL0 (hfsu : FSU G T L I)
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    ⁅fsuV T I, fsuL0 T L⁆ = fsuV T I := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    have h1 : l * v⁻¹ * l⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (hN (le_sup_left (a := fsuL0 T L) hl)) _).mp
        (Subgroup.inv_mem _ hv)
    have e : v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hv h1
  · have hI : I ≤ ⁅fsuV T I, fsuL0 T L⁆ :=
      calc I = ⁅I, fsuL0 T L⁆ := hfsu.irrPlus.2.2.2.1.symm
        _ ≤ ⁅fsuV T I, fsuL0 T L⁆ := Subgroup.commutator_mono (le_fsuV I T) le_rfl
    apply conjClosure_le
    intro t ht i hi
    exact conj_mem_commutator (hN (le_sup_right (b := T) ht)) (le_normalizer_conjClosure L T ht)
      (hI hi)

theorem fsuV_inf_centralizer_eq_bot (hfsu : FSU G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hcen : centerOf (fsuL0 T L ⊔ T) = ⊥) :
    fsuV T I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ := by
  set C := fsuV T I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) with hCdef
  have hT2 : IsPGroup 2 T := hfsu.sylow.1
  have : Group.IsNilpotent T := hT2.isNilpotent
  have hCT : C ≤ T := inf_le_left.trans (fsuV_le_T hfsu hV hN)
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    have hfwd : ∀ s ∈ T, ∀ c ∈ C, s * c * s⁻¹ ∈ C := by
      intro s hs c hc
      refine Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (hN (le_sup_right (b := T) hs)) c).mp hc.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : s⁻¹ * l * s ∈ fsuL0 T L := by
        have := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_conjClosure L T (T.inv_mem hs)) l).mp hl
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 _ hl'
      calc l * (s * c * s⁻¹) = s * ((s⁻¹ * l * s) * c) * s⁻¹ := by group
        _ = s * (c * (s⁻¹ * l * s)) * s⁻¹ := by rw [hcomm]
        _ = s * c * s⁻¹ * l := by group
    intro c
    refine ⟨hfwd t ht c, fun hc => ?_⟩
    have := hfwd t⁻¹ (T.inv_mem ht) _ hc
    simpa [mul_assoc] using this
  by_contra hne
  have hnormal : (C.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCT).mpr hTC
  have hne' : C.subgroupOf T ≠ ⊥ := by
    intro h
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hCT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  have hyC : (y : G) ∈ C := hy.1
  have hyT : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  have hyZ : (y : G) ∈ centerOf (fsuL0 T L ⊔ T) := by
    refine Subgroup.mem_inf.mpr ⟨le_sup_right (a := fsuL0 T L) y.2, ?_⟩
    have hle : fsuL0 T L ⊔ T ≤ Subgroup.centralizer ({(y : G)} : Set G) := by
      refine sup_le (fun l hl => ?_) (fun t ht => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hyC.2 l hl
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hyT t ht
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx))
  rw [hcen, Subgroup.mem_bot] at hyZ
  exact hy1 (Subtype.ext (Subtype.ext hyZ))

theorem fsuV_inf_centralizer_T_ne_bot (hfsu : FSU G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    fsuV T I ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ := by
  intro h
  apply fsuV_inf_omegaOneCenter_ne_bot hfsu hV hN
  rw [eq_bot_iff, ← h]
  exact inf_le_inf_left _ (fun z hz => (Subgroup.closure_le _).mpr
    (fun x hx => hx.1.2) hz)

theorem fsuV_cases_of_normal (h325 : Stmt3_2_5) (hyp : Hyp7_0_2 G T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    I = fsuV T I ∨ ∃ t ∈ T, fsuV T I = I ⊔ CFSG.conjugate I t ∧
      I ⊓ CFSG.conjugate I t = ⊥ ∧ ¬ IsXSectionIso₂ L I ⊥ (CFSG.conjugate I t) ⊥ ∧
      I ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have hL : L = conjClosure L T := (fsuL0_eq_of_le_normalizer hTL).symm
  obtain ⟨-, -, h3⟩ := h325 G T L I hyp.fsu hL
  rcases h3 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨hC, -, ⟨t, ht, htN⟩, hall⟩
  · exact Or.inl h
  · exact Or.inl h
  · obtain ⟨-, hsum, hinf, hniso⟩ := hall t ht htN
    exact Or.inr ⟨t, ht, hsum, hinf, hniso, hC⟩

theorem irr_of_inf_centralizer (hfsu : FSU G T L I)
    (hC : I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥) :
    ∀ J : Subgroup G, J ≤ I → fsuL0 T L ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = I := by
  intro J hJI hJN
  have h := hfsu.irrPlus.2.2.2.2.2.1 J (by rw [hC]; exact bot_le) hJI hJN
  rwa [hC] at h

theorem fsuV_eq_conjClosure_of_normal (h325 : Stmt3_2_5) (hyp : Hyp7_0_2 G T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hcen : centerOf (fsuL0 T L ⊔ T) = ⊥) :
    fsuV T I = conjClosure (fsuV T I ⊓ Subgroup.centralizer (T : Set G)) (fsuL0 T L) := by
  set W := conjClosure (fsuV T I ⊓ Subgroup.centralizer (T : Set G)) (fsuL0 T L) with hWdef
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hLV : fsuL0 T L ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_left.trans hN
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hWV : W ≤ fsuV T I := conjClosure_le fun l hl x hx =>
    (Subgroup.mem_normalizer_iff.mp (hLV hl) x).mp hx.1
  have hWL : fsuL0 T L ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure _ _
  have hWT : T ≤ Subgroup.normalizer (W : Set G) := by
    intro t ht
    refine mem_normalizer_conjClosure ?_ (le_normalizer_conjClosure L T ht)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hfwd : ∀ s ∈ T, ∀ y ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G),
        s * y * s⁻¹ ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
      intro s hs y hy
      have hys : s * y * s⁻¹ = y := by
        rw [Subgroup.mem_centralizer_iff.mp hy.2 s hs, mul_inv_cancel_right]
      rw [hys]
      exact hy
    refine ⟨hfwd t ht x, fun hx => ?_⟩
    have := hfwd t⁻¹ (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hW0 : W ≠ ⊥ := by
    intro h
    apply fsuV_inf_centralizer_T_ne_bot hyp.fsu hV hN
    rw [eq_bot_iff, ← h]
    exact le_conjClosure _ _
  have hCV := fsuV_inf_centralizer_eq_bot hyp.fsu hV hN hcen
  have hCI : I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hCV]
    exact inf_le_inf_right _ (le_fsuV I T)
  have hirr := irr_of_inf_centralizer hyp.fsu hCI
  rcases fsuV_cases_of_normal h325 hyp hTL with hIV | ⟨t, ht, hsum, hinf, hniso, -⟩
  ·
    rcases hirr W (hIV ▸ hWV) hWL with h | h
    · exact absurd h hW0
    · exact hIV.symm.trans h.symm
  ·
    have hItV : CFSG.conjugate I t ≤ fsuV T I := hsum ▸ le_sup_right
    have hIV : I ≤ fsuV T I := le_fsuV I T
    have htL0 : t ∈ Subgroup.normalizer (fsuL0 T L : Set G) := le_normalizer_conjClosure L T ht
    have hIN : fsuL0 T L ≤ Subgroup.normalizer (I : Set G) := hyp.fsu.irrPlus.2.2.1
    have hItN : fsuL0 T L ≤ Subgroup.normalizer (CFSG.conjugate I t : Set G) :=
      le_normalizer_conjugate htL0 hIN
    have hirr' : ∀ J : Subgroup G, J ≤ CFSG.conjugate I t →
        fsuL0 T L ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = CFSG.conjugate I t := by
      intro J hJ hJN
      have hJ' : CFSG.conjugate J t⁻¹ ≤ I := by
        have := conjugate_mono hJ t⁻¹
        rwa [conjugate_conjugate_inv'] at this
      have hJN' := le_normalizer_conjugate (Subgroup.inv_mem _ htL0) hJN
      have hJJ : J = CFSG.conjugate (CFSG.conjugate J t⁻¹) t := by
        have := conjugate_conjugate_inv' J t⁻¹
        rw [inv_inv] at this
        exact this.symm
      rcases hirr _ hJ' hJN' with h | h
      · left
        rw [hJJ, h]
        exact Subgroup.map_bot _
      · right
        rw [hJJ, h]
    have hWt : ∀ g ∈ T, CFSG.conjugate W g = W := fun g hg =>
      conjugate_eq_of_mem_normalizer (hWT hg)
    rcases hirr (W ⊓ I) inf_le_right (le_normalizer_inf hWL hIN) with h1 | h1
    · rcases hirr' (W ⊓ CFSG.conjugate I t) inf_le_right (le_normalizer_inf hWL hItN) with
        h2 | h2
      ·
        exfalso
        apply hW0
        have hcomm : IsMulCommutative ↥(fsuV T I) := hV.1
        have hnoniso : ¬ SecIsoL (autOn (fsuL0 T L) (fsuV T I)) (I.subgroupOf (fsuV T I)) ⊥
            ((CFSG.conjugate I t).subgroupOf (fsuV T I)) ⊥ := by
          rw [hL0]
          rw [hL0] at hLV hIN hItN
          exact InternalSec.not_secIsoL_of_not_isXSectionIso₂ hIV hItV hLV hIN hItN hniso
        have hJ := InternalSec.eq_bot_of_diag
          (InternalSec.sup_subgroupOf_eq_top hIV hItV hsum.symm)
          (InternalSec.inf_subgroupOf_eq_bot hinf)
          (InternalSec.autOn_inv_subgroupOf hIN) (InternalSec.autOn_inv_subgroupOf hItN)
          (InternalSec.irr_subgroupOf hLV fun J hJ hJN => hirr J hJ hJN)
          (InternalSec.irr_subgroupOf hLV fun J hJ hJN => hirr' J hJ hJN) hnoniso
          (J := W.subgroupOf (fsuV T I)) (InternalSec.autOn_inv_subgroupOf hWL)
          (inf_subgroupOf_eq_bot_of h1) (inf_subgroupOf_eq_bot_of h2)
        rw [eq_bot_iff]
        intro w hw
        have : (⟨w, hWV hw⟩ : ↥(fsuV T I)) ∈ W.subgroupOf (fsuV T I) := hw
        rw [hJ, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
      ·
        have hItW : CFSG.conjugate I t ≤ W := h2 ▸ inf_le_left
        have hIW : I ≤ W := by
          have := conjugate_mono hItW t⁻¹
          rwa [conjugate_conjugate_inv', hWt t⁻¹ (T.inv_mem ht)] at this
        exact le_antisymm (hsum ▸ sup_le hIW hItW) hWV
    ·
      have hIW : I ≤ W := h1 ▸ inf_le_left
      have hItW : CFSG.conjugate I t ≤ W := hWt t ht ▸ conjugate_mono hIW t
      exact le_antisymm (hsum ▸ sup_le hIW hItW) hWV

theorem not_isFFModule_autOn_sup (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    ∃ _ : IsMulCommutative ↥(fsuV T I),
      ¬ IsFFModule (V := ↥(fsuV T I)) (autOn (fsuL0 T L ⊔ T) (fsuV T I)) := by
  have hc : IsMulCommutative ↥(fsuV T I) := hV.1
  refine ⟨hc, fun hFF => ?_⟩
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender hFF
  exact not_isFFStarOffender_autOn h37 h38 h39 hyp hV hN hc ⟨A, hA⟩

theorem not_orth (hyp : Hyp7_0_2 G T L I) {n : ℕ} (hn : 1 ≤ n)
    (h : ∃ _ : IsMulCommutative ↥(fsuV T I),
      BinaryOrthogonalFour (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ n) : False := by
  obtain ⟨hc, h⟩ := h
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · exact hyp.notOrth hc ⟨n, h1, h⟩
  · have hn1 : n = 1 := le_antisymm h1 hn
    subst hn1
    obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender
      (OrthFF.isFFModule_normalizer_of_binaryOrthogonalFour_one h)
    exact hyp.notFF hc ⟨A, hA⟩

theorem not_fano_of_normal (h325 : Stmt3_2_5) (hyp : Hyp7_0_2 G T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hcen : centerOf (fsuL0 T L ⊔ T) = ⊥)
    (h : ∃ _ : IsMulCommutative ↥(fsuV T I),
      FanoCoreModule (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥) : False := by
  obtain ⟨hc, h⟩ := h
  have hcard : Nat.card ↥(fsuV T I) = 64 := Fano.FanoCoreModule.card h
  have hLV : fsuL0 T L ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_left.trans hN
  have hCV := fsuV_inf_centralizer_eq_bot hyp.fsu hV hN hcen
  have hCI : I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hCV]
    exact inf_le_inf_right _ (le_fsuV I T)
  have hirr := irr_of_inf_centralizer hyp.fsu hCI
  have hIN : fsuL0 T L ≤ Subgroup.normalizer (I : Set G) := hyp.fsu.irrPlus.2.2.1
  have hIV : I ≤ fsuV T I := le_fsuV I T
  have hcardI : ∀ {X : Subgroup G}, X ≤ fsuV T I →
      Nat.card ↥(X.subgroupOf (fsuV T I)) = Nat.card ↥X := fun hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  rcases fsuV_cases_of_normal h325 hyp hTL with hIVeq | ⟨t, ht, hsum, hinf, -, -⟩
  ·
    obtain ⟨X, hX, hX8⟩ := Fano.FanoCoreModule.exists_card_eight h
    have hirr' := InternalSec.irr_subgroupOf hLV fun J hJ hJN => hirr J hJ hJN
    have htop : I.subgroupOf (fsuV T I) = ⊤ := by
      rw [← hIVeq] at hIV ⊢
      exact Subgroup.subgroupOf_self _
    rcases hirr' X (htop ▸ le_top) hX with h0 | h0
    · rw [h0, Subgroup.card_bot] at hX8
      norm_num at hX8
    · rw [h0, htop, Subgroup.card_top, hcard] at hX8
      norm_num at hX8
  ·
    have hItV : CFSG.conjugate I t ≤ fsuV T I := hsum ▸ le_sup_right
    have hItN : fsuL0 T L ≤ Subgroup.normalizer (CFSG.conjugate I t : Set G) :=
      le_normalizer_conjugate (le_normalizer_conjClosure L T ht) hIN
    have hsum' := InternalSec.sup_subgroupOf_eq_top hIV hItV hsum.symm
    have hinf' := InternalSec.inf_subgroupOf_eq_bot (V := fsuV T I) hinf
    have hprod : Nat.card ↥(fsuV T I) = Nat.card ↥I * Nat.card ↥I := by
      rw [← Nat.card_congr (InternalSec.sumEquiv hsum' hinf').toEquiv, Nat.card_prod,
        hcardI hIV, hcardI hItV, card_conjugate]
    have hI8 : Nat.card ↥I = 8 := by
      rw [hcard] at hprod
      exact le_antisymm (by nlinarith) (by nlinarith)
    have heq := Fano.FanoCoreModule.eq_of_card_eight h
      (InternalSec.autOn_inv_subgroupOf hIN) (InternalSec.autOn_inv_subgroupOf hItN)
      (by rw [hcardI hIV, hI8]) (by rw [hcardI hItV, card_conjugate, hI8])
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hIV, inf_eq_left.mpr hItV] at heq
    apply hyp.fsu.irrPlus.2.1
    rw [← hinf, ← heq, inf_idem]

theorem centerOf_eq_bot_of_normal (hC58 : TheoremC58) (h317 : AS317Sylow) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) : centerOf (fsuL0 T L ⊔ T) = ⊥ := by
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hJ := thompsonJ_le_centralizer_fsuV h37 h38 h39 hyp hV hN
  rcases theorem318_three hC58 h317 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow
      (hyp318_of_normal h37 h38 h39 h3228 hyp hTL hH) with ⟨hJ', -⟩ | ⟨-, -, hZ⟩
  · exact absurd (le_inf (iSup₂_le fun _ hA => hA.1) hJ) hJ'
  · exact hZ

theorem local_structure_of_normal (h4414 : Stmt4_4_14) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight)
    (h325 : Stmt3_2_5) (hyp : Hyp7_0_2 G T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∀ H : Subgroup G, IsHStar T (fsuM T L) H → 1 < E1.nParam H →
      H ⊓ fsuM T L = H ⊓ Subgroup.normalizer (fsuV T I : Set G) ∧
        H ⊓ fsuM T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (H ⊓ fsuM T L) := by
  intro H hH hn
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hloc1 := inf_fsuM_eq_of_normal hC58 h317 h37 h38 h39 h3228 h325 hyp hTL hH
  have hcen := centerOf_eq_bot_of_normal hC58 h317 h37 h38 h39 h3228 hyp hTL hH
  refine ⟨hloc1, ?_⟩
  have hU := lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 h39
    hyp.fsu.sylow hyp.fsu.maximal
  obtain ⟨hVX, hred, -⟩ := h3228 G T L I hyp.fsu
  have hcomm := commutator_fsuV_fsuL0 hyp.fsu hN
  rcases h4414 G T (fsuM T L) L (fsuV T I) H hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.sylow hU.1.1 (le_sup_right.trans hU.1.2) hyp.fsu.maximal hyp.fsu.faithful
      (le_sup_left.trans hU.1.2) hyp.fsu.quasisimple hVX hred hH
      (by rw [hcomm]; exact fsuV_ne_bot hyp.fsu)
      (fsuV_eq_conjClosure_of_normal h325 hyp hTL hV hN hcen)
      (by rw [hcomm]; exact not_isFFModule_autOn_sup h37 h38 h39 hyp hV hN) hn with
    ⟨h2c, hfaith⟩ | ⟨n, hn1, -, h2⟩ | ⟨-, h3⟩
  · exact inf_centralizer_le_of_faithful h3228 hyp hTL hloc1 h2c hfaith
  · rw [hcomm] at h2
    exact (not_orth hyp hn1 h2).elim
  · rw [hcomm] at h3
    exact (not_fano_of_normal h325 hyp hTL hV hN hcen h3).elim

end CFSG.Quasithin.H13
