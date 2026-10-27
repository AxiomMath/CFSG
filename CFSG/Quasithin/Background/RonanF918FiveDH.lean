module

public import CFSG.Quasithin.Background.RonanF918FiveDG

public section

namespace CFSG.Quasithin.RonanF918

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.RonanD321.SL2Model
open scoped Matrix

section ModStab

variable {W : Type} [CommGroup W] [Finite W]

theorem mem_stabSub_of_forall_mem {U : Subgroup W} {g : MulAut W} (h : ∀ u ∈ U, g u ∈ U) :
    g ∈ stabSub U := by
  have hle : U.map g.toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  have hcard : Nat.card ↥(U.map g.toMonoidHom) = Nat.card ↥U :=
    Subgroup.card_map_of_injective g.injective
  have heq : U.map g.toMonoidHom = U :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  intro u
  constructor
  · intro hu
    rw [← heq] at hu
    obtain ⟨u', hu', hu'u⟩ := hu
    have : u' = u := g.injective hu'u
    rwa [← this]
  · exact h u

theorem commSub_apply_mem {S : Subgroup W} {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W))) (hS : ∀ s ∈ S, g s ∈ S) {r : W}
    (hr : r ∈ commSub S L) : g r ∈ commSub S L := by
  induction hr using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, s, hs, rfl⟩ := hc
    have hx' : g * x * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    refine Subgroup.subset_closure ⟨g * x * g⁻¹, hx', g s, hS s hs, ?_⟩
    simp [MulAut.mul_apply]
  | one => simpa using (commSub S L).one_mem
  | mul a b ha hb iha ihb => simpa [map_mul] using (commSub S L).mul_mem iha ihb
  | inv a ha ih => simpa [map_inv] using (commSub S L).inv_mem ih

end ModStab

section LineStab

variable {F : Type} [Field F]

theorem multOpU_mem_multLineModuleU {line : Submodule F (Fin 2 → F)}
    {B : Matrix.GeneralLinearGroup (Fin 2) F}
    (hB : ∀ v ∈ line, (B : Matrix (Fin 2) (Fin 2) F).mulVec v ∈ line)
    {Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)} (hY : Y ∈ multLineModuleU F line) :
    multOpU F B Y ∈ multLineModuleU F line := by
  intro row
  have e : (fun column => Multiplicative.toAdd (multOpU F B Y) row column) =
      (B : Matrix (Fin 2) (Fin 2) F).mulVec (fun k => Multiplicative.toAdd Y row k) := by
    funext column
    simp only [multOpU, toAdd_ofAdd, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  show (fun column => Multiplicative.toAdd (multOpU F B Y) row column) ∈ line
  rw [e]
  exact hB _ (hY row)

variable {W : Type} [CommGroup W] [Finite W] {L Mp : Subgroup (MulAut W)}
  (D : CoordData L Mp F) (line : Submodule F (Fin 2 → F))

theorem Sline_apply_mem (g : ↥(NLM L Mp))
    (hg : ∀ Y ∈ multLineModuleU F line, psi D g Y ∈ multLineModuleU F line) {s : W}
    (hs : s ∈ Sline D line) : (g : MulAut W) s ∈ Sline D line := by
  have hsC : s ∈ commV L := Sline_le_commV D line hs
  have hgsC : (g : MulAut W) s ∈ commV L := apply_mem_commV g.2.1 hsC
  rw [mem_Sline_iff D line ⟨_, hgsC⟩]
  have h1 : D.bq ⟨(g : MulAut W) s, hgsC⟩ = psi D g (D.bq ⟨s, hsC⟩) := by
    rw [psi_apply, psi0_apply]
    rfl
  rw [h1]
  exact hg _ ((mem_Sline_iff D line ⟨s, hsC⟩).mp hs)

end LineStab

section AutOnComm

open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem map_commSub_autOn_eq {X V : Subgroup G} [IsMulCommutative V]
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (S : Subgroup ↥V) :
    (commSub S (autOn X V)).map V.subtype = ⁅S.map V.subtype, X⁆ := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, commSub, Subgroup.closure_le]
    rintro _ ⟨σ, hσ, v, hv, rfl⟩
    obtain ⟨g, hgX, rfl⟩ := AutOn.mem_autOn_iff.1 hσ
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    show ((conjAct V g v * v⁻¹ : V) : G) ∈ ⁅S.map V.subtype, X⁆
    rw [Subgroup.coe_mul, AutOn.coe_conjAct_apply, Subgroup.coe_inv]
    have e : (g : G) * v * (g : G)⁻¹ * (v : G)⁻¹ = ⁅(v : G), (g : G)⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (⁅S.map V.subtype, X⁆).inv_mem (Subgroup.commutator_mem_commutator ⟨v, hv, rfl⟩ hgX)
  · rw [Subgroup.commutator_le]
    rintro _ ⟨w, hw, rfl⟩ k hk
    have hmem : conjAct V ⟨k, hXV hk⟩ w * w⁻¹ ∈ commSub S (autOn X V) :=
      Subgroup.subset_closure ⟨_, AutOn.conjAct_mem_autOn ⟨k, hXV hk⟩ hk, w, hw, rfl⟩
    refine ⟨(conjAct V ⟨k, hXV hk⟩ w * w⁻¹)⁻¹, (commSub S (autOn X V)).inv_mem hmem, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, AutOn.coe_conjAct_apply]
    rw [commutatorElement_def]
    group

end AutOnComm

section Cases

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}
  [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

@[expose] noncomputable def Spre (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hV₁I : V₁ ≤ I) {F : Type} [Field F]
    (D : CoordData (autIH V₁ I H K) (autIH V₁ I H (conjClosure K T)) F)
    (line : Submodule F (Fin 2 → F)) : Subgroup G :=
  ((multLineModuleU F line).comap (D.bq.comp (Jt h hIU hV₁I))).map
    (V₁ ⊔ ⁅conjClosure I H, K⁆).subtype

variable (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (hV₁I : V₁ ≤ I) {F : Type}
  [Field F] (D : CoordData (autIH V₁ I H K) (autIH V₁ I H (conjClosure K T)) F)
  (line : Submodule F (Fin 2 → F))

theorem Spre_le : Spre h hIU hV₁I D line ≤ V₁ ⊔ ⁅conjClosure I H, K⁆ :=
  Subgroup.map_subtype_le _

theorem mem_Spre_iff {x : G} :
    x ∈ Spre h hIU hV₁I D line ↔ ∃ hx : x ∈ V₁ ⊔ ⁅conjClosure I H, K⁆,
      D.bq (Jt h hIU hV₁I ⟨x, hx⟩) ∈ multLineModuleU F line := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hlm⟩
    exact ⟨⟨x, hx⟩, hlm, rfl⟩

theorem tildeOf_Spre_eq :
    tildeOf V₁ (Spre h hIU hV₁I D line) =
      (Sline D line).map (tildeOf V₁ (conjClosure I H)).subtype := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hxS, rfl⟩ := mem_secImg.mp hy
    obtain ⟨hxJ, hlm⟩ := (mem_Spre_iff h hIU hV₁I D line).mp hxS
    refine ⟨((Jt h hIU hV₁I ⟨(x : G), hxJ⟩ : ↥(commV (autIH V₁ I H K))) :
      ↥(tildeOf V₁ (conjClosure I H))), (mem_Sline_iff D line _).mpr hlm, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    have hwC : (w : ↥(tildeOf V₁ (conjClosure I H))) ∈ commV (autIH V₁ I H K) :=
      Sline_le_commV D line hw
    have hbq : D.bq ⟨w, hwC⟩ ∈ multLineModuleU F line := (mem_Sline_iff D line ⟨w, hwC⟩).mp hw
    obtain ⟨v, hv⟩ := Jt_surjective h hIU hV₁I ⟨w, hwC⟩
    have hvS : ((v : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆)) : G) ∈ Spre h hIU hV₁I D line :=
      (mem_Spre_iff h hIU hV₁I D line).mpr ⟨v.2, by
        have : (⟨(v : G), v.2⟩ : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆)) = v := rfl
        rw [this, hv]
        exact hbq⟩
    have hmk := secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (x := ⟨(v : G), Jg_le_normalizer h hIU hV₁I v.2⟩) hvS
    have heq : (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
        secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨(v : G), Jg_le_normalizer h hIU hV₁I v.2⟩ :=
      (congrArg (fun u : ↥(commV (autIH V₁ I H K)) =>
        ((u : ↥(tildeOf V₁ (conjClosure I H))) : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) hv).symm
    show (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈ _
    rw [heq]
    exact hmk

theorem Spre_le_conjClosure : Spre h hIU hV₁I D line ≤ conjClosure I H :=
  (Spre_le h hIU hV₁I D line).trans (Jg_le_conjClosure h hV₁I)

theorem commutator_Spre_le : ⁅Spre h hIU hV₁I D line, K⁆ ≤ conjClosure I H :=
  (Subgroup.commutator_mono (Spre_le_conjClosure h hIU hV₁I D line) le_rfl).trans
    (commutator_le_conjClosure_K h)

theorem Jline_le_conjClosure : V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆ ≤ conjClosure I H := by
  refine sup_le ?_ ?_
  · exact hV₁I.trans (le_conjClosure I H)
  · exact commutator_Spre_le h hIU hV₁I D line

theorem Jline_le_Jg : V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆ ≤ V₁ ⊔ ⁅conjClosure I H, K⁆ := by
  refine sup_le le_sup_left ?_
  exact (Subgroup.commutator_mono (Spre_le_conjClosure h hIU hV₁I D line) le_rfl).trans le_sup_right

theorem subM_Jline_eq :
    subM V₁ (conjClosure I H) (V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆) =
      commSub (Sline D line) (autIH V₁ I H K) := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hKN : K ≤ Subgroup.normalizer (V₁ : Set G) := hKH.trans h.H_le_normalizer_V₁
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hSN : Spre h hIU hV₁I D line ≤ Subgroup.normalizer (V₁ : Set G) :=
    (Spre_le_conjClosure h hIU hV₁I D line).trans hIHN
  have hcommN : ⁅Spre h hIU hV₁I D line, K⁆ ≤ Subgroup.normalizer (V₁ : Set G) :=
    (commutator_Spre_le h hIU hV₁I D line).trans hIHN
  haveI : IsMulCommutative ↥(tildeOf V₁ (conjClosure I H)) :=
    (Fact.out : IsElemAbelian 2 (tildeOf V₁ (conjClosure I H))).1
  apply Subgroup.map_injective (tildeOf V₁ (conjClosure I H)).subtype_injective
  have e1 : (subM V₁ (conjClosure I H) (V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆)).map
      (tildeOf V₁ (conjClosure I H)).subtype =
      tildeOf V₁ (V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆) :=
    map_subtype_subM (secImg_mono (Jline_le_conjClosure h hIU hV₁I D line))
  have e2 : tildeOf V₁ (V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆) =
      tildeOf V₁ ⁅Spre h hIU hV₁I D line, K⁆ := by
    rw [sup_comm]
    exact tildeOf_sup_self hcommN
  have e3 : tildeOf V₁ ⁅Spre h hIU hV₁I D line, K⁆ =
      ⁅tildeOf V₁ (Spre h hIU hV₁I D line), tildeOf V₁ K⁆ := tildeOf_commutator' hSN hKN
  have hXV : tildeOf V₁ K ≤ Subgroup.normalizer
      ((tildeOf V₁ (conjClosure I H) : Subgroup (GtOf V₁)) : Set (GtOf V₁)) :=
    secImg_le_normalizer_secImg (hKH.trans (le_normalizer_conjClosure I H))
  have e4 := map_commSub_autOn_eq hXV (Sline D line)
  rw [e1, e2, e3, tildeOf_Spre_eq h hIU hV₁I D line]
  exact e4.symm

theorem mem_normalizer_Jline (g : ↥(NLM (autIH V₁ I H K) (autIH V₁ I H (conjClosure K T)))) (x : ↥H)
    (hgx : (g : MulAut ↥(tildeOf V₁ (conjClosure I H))) =
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x)
    (hS : ∀ Y ∈ multLineModuleU F line, psi D g Y ∈ multLineModuleU F line) :
    (x : G) ∈ Subgroup.normalizer ((V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆ : Subgroup G) : Set G) := by
  refine (actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
    (le_normalizer_conjClosure I H) le_sup_left (Jline_le_conjClosure h hIU hV₁I D line) x).mp ?_
  rw [subM_Jline_eq h hIU hV₁I D line, ← hgx]
  exact mem_stabSub_of_forall_mem fun r hr => commSub_apply_mem g.2.1
    (fun s hs => Sline_apply_mem D line g hS hs) hr

theorem K_le_normalizer_Jline :
    K ≤ Subgroup.normalizer ((V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆ : Subgroup G) : Set G) := by
  intro k hk
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  refine (actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
    (le_normalizer_conjClosure I H) le_sup_left (Jline_le_conjClosure h hIU hV₁I D line)
    ⟨k, hKH hk⟩).mp ?_
  rw [subM_Jline_eq h hIU hV₁I D line]
  have hl : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨k, hKH hk⟩ ∈
      autIH V₁ I H K := by
    rw [autIH_eq_map h hKH]
    exact ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  exact mem_stabSub_of_forall_mem fun r hr =>
    commSub_invariant (fun l hl s hs => Sline_invariant D line hl hs) hl hr

theorem tildeOf_commutator_Jline :
    tildeOf V₁ ⁅V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆, K⁆ =
      tildeOf V₁ (V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆) := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hKN : K ≤ Subgroup.normalizer (V₁ : Set G) := hKH.trans h.H_le_normalizer_V₁
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hJN : V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆ ≤ Subgroup.normalizer (V₁ : Set G) :=
    (Jline_le_conjClosure h hIU hV₁I D line).trans hIHN
  haveI : IsMulCommutative ↥(tildeOf V₁ (conjClosure I H)) :=
    (Fact.out : IsElemAbelian 2 (tildeOf V₁ (conjClosure I H))).1
  haveI : Group.IsPerfect ↥(autIH V₁ I H K) := F918Fine4Pf.isPerfect_autIH h I
  have hXV : tildeOf V₁ K ≤ Subgroup.normalizer
      ((tildeOf V₁ (conjClosure I H) : Subgroup (GtOf V₁)) : Set (GtOf V₁)) :=
    secImg_le_normalizer_secImg (hKH.trans (le_normalizer_conjClosure I H))
  have e1 : (subM V₁ (conjClosure I H) (V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆)).map
      (tildeOf V₁ (conjClosure I H)).subtype =
      tildeOf V₁ (V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆) :=
    map_subtype_subM (secImg_mono (Jline_le_conjClosure h hIU hV₁I D line))
  rw [tildeOf_commutator' hJN hKN, ← e1,
    ← map_commSub_autOn_eq hXV (subM V₁ (conjClosure I H) (V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆)),
    subM_Jline_eq h hIU hV₁I D line,
    commSub_commSub_eq_of_perfect (fun l hl s hs => Sline_invariant D line hl hs)]

theorem centralizerMod_Jline_lt (hrank : Module.finrank F line = 1) :
    centralizerMod V₁ (V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆) K <
      V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆ := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hLMp : autIH V₁ I H K ≤ autIH V₁ I H (conjClosure K T) := autIH_K_le_K₀ (V₁ := V₁) I hKH T
  refine lt_of_le_of_ne (centralizerMod_le_left V₁ _ K) fun heq => ?_
  have h1 := subM_centralizerMod h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
    (le_normalizer_conjClosure I H) hKH (le_sup_left : V₁ ≤ V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆)
    (Jline_le_conjClosure h hIU hV₁I D line)
  rw [heq, subM_Jline_eq h hIU hV₁I D line] at h1
  have hlt := (isIrrSec_commSub D line hLMp hrank).1
  rw [← h1] at hlt
  exact lt_irrefl _ hlt

theorem Jline_irreducible (hrank : Module.finrank F line = 1) :
    ∀ J' : Subgroup G, V₁ ≤ J' → J' ≤ V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆ →
      K ≤ Subgroup.normalizer (J' : Set G) →
      centralizerMod V₁ (V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆) K ≤ J' →
      J' = centralizerMod V₁ (V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆) K ∨
        J' = V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆ := by
  intro J' hV₁J' hJ'J hKJ' hCJ'
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hLMp : autIH V₁ I H K ≤ autIH V₁ I H (conjClosure K T) := autIH_K_le_K₀ (V₁ := V₁) I hKH T
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hirr : XMod.IsIrrSec ↥(autIH V₁ I H K)
      (subM V₁ (conjClosure I H) (centralizerMod V₁ (V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆) K))
      (subM V₁ (conjClosure I H) (V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆)) := by
    rw [subM_centralizerMod h.H_le_normalizer_V₁ hIHN (le_normalizer_conjClosure I H) hKH
      (le_sup_left : V₁ ≤ V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆)
      (Jline_le_conjClosure h hIU hV₁I D line), subM_Jline_eq h hIU hV₁I D line]
    exact isIrrSec_commSub D line hLMp hrank
  exact eq_or_eq_of_isIrrSec h.H_le_normalizer_V₁ hIHN (le_normalizer_conjClosure I H) hKH
    (le_centralizerMod h.H_le_normalizer_V₁ hKH le_sup_left) hCJ' hJ'J
    (Jline_le_conjClosure h hIU hV₁I D line) hKJ' hirr

theorem isIrrPlusTilde_Jline (hrank : Module.finrank F line = 1) :
    IsIrrPlusTilde V₁ K (V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆) :=
  ⟨K_le_normalizer_Jline h hIU hV₁I D line, tildeOf_commutator_Jline h hIU hV₁I D line,
    centralizerMod_Jline_lt h hIU hV₁I D line hrank, Jline_irreducible h hIU hV₁I D line hrank⟩

end Cases

end CFSG.Quasithin.RonanF918
