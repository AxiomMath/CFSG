module

public import CFSG.Quasithin.Background.F918Z5A3
public import CFSG.Quasithin.Background.RonanF918FiveC

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped Pointwise commutatorElement

section Conj

variable {G : Type} [Group G]

theorem pCoreOf_subgroupOf_self (J : Subgroup G) :
    (pCoreOf 2 J).subgroupOf J = CFSG.pCore 2 ↥J := by
  unfold pCoreOf
  exact Subgroup.comap_map_eq_self_of_injective J.subtype_injective (CFSG.pCore 2 ↥J)

theorem isQuasisimple_conjSub_pCoreOf {J : Subgroup G}
    (hJq : CFSG.IsQuasisimple (↥J ⧸ (pCoreOf 2 J).subgroupOf J)) (x : G) :
    CFSG.IsQuasisimple (↥(conjSub x J) ⧸ (pCoreOf 2 (conjSub x J)).subgroupOf (conjSub x J)) := by
  let e : ↥J ≃* ↥(conjSub x J) := (MulAut.conj x).subgroupMap J
  have e1 : ↥J ⧸ (pCoreOf 2 J).subgroupOf J ≃* ↥J ⧸ CFSG.pCore 2 ↥J :=
    QuotientGroup.quotientMulEquivOfEq (pCoreOf_subgroupOf_self J)
  have e2 : ↥(conjSub x J) ⧸ (pCoreOf 2 (conjSub x J)).subgroupOf (conjSub x J) ≃*
      ↥(conjSub x J) ⧸ CFSG.pCore 2 ↥(conjSub x J) :=
    QuotientGroup.quotientMulEquivOfEq (pCoreOf_subgroupOf_self (conjSub x J))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e2.symm
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr (CFSG.pCore 2 ↥J) (CFSG.pCore 2 ↥(conjSub x J)) e
        (CFSG.pCore_map_iso 2 e))
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv e1 hJq))

theorem conjClosure_conjSub_eq {K T : Subgroup G} {t : G} (ht : t ∈ T) :
    conjClosure (conjSub t K) T = conjClosure K T := by
  apply le_antisymm
  · refine conjClosure_le fun h hh z hz => ?_
    have hz' : t⁻¹ * z * t ∈ K := mem_conjSub.mp hz
    have e : (h * t) * (t⁻¹ * z * t) * (h * t)⁻¹ = h * z * h⁻¹ := by group
    rw [← e]
    exact Subgroup.subset_closure ⟨h * t, T.mul_mem hh ht, _, hz', rfl⟩
  · refine conjClosure_le fun h hh k hk => ?_
    have hz : t * k * t⁻¹ ∈ conjSub t K := by
      rw [mem_conjSub]
      have e : t⁻¹ * (t * k * t⁻¹) * t = k := by group
      rw [e]
      exact hk
    have e : (h * t⁻¹) * (t * k * t⁻¹) * (h * t⁻¹)⁻¹ = h * k * h⁻¹ := by group
    rw [← e]
    exact Subgroup.subset_closure ⟨h * t⁻¹, T.mul_mem hh (T.inv_mem ht), _, hz, rfl⟩

variable {T V L V₁ Vp H K : Subgroup G}

theorem hypF918_conj (h : HypF918 T V L V₁ Vp H K) {t : G} (htT : t ∈ T) :
    HypF918 T V L V₁ Vp H (conjSub t K) :=
  ⟨h.toHypF98, map_conj_mem_cComp h.K_cComp (h.T_le_H htT),
    isQuasisimple_conjSub_pCoreOf h.K_quasisimple t,
    by rw [conjClosure_conjSub_eq htT]; exact h.H_eq,
    by rw [conjClosure_conjSub_eq htT]; exact h.K₀_normal⟩

end Conj

section ConjFacts

variable {G : Type} [Group G]

theorem conjSub_eq_conjSub_inv_of_sq {t : G} {K : Subgroup G}
    (hsq : t * t ∈ Subgroup.normalizer (K : Set G)) : conjSub t K = conjSub t⁻¹ K := by
  have h1 : conjSub (t * t) K = K := A38.map_conj_eq_iff.mpr hsq
  calc conjSub t K = conjSub (t⁻¹ * (t * t)) K := by rw [inv_mul_cancel_left]
    _ = conjSub t⁻¹ (conjSub (t * t) K) := conjSub_mul _ _ _
    _ = conjSub t⁻¹ K := by rw [h1]

theorem not_mem_normalizer_conjSub {t : G} {K : Subgroup G}
    (htK : t ∉ Subgroup.normalizer (K : Set G)) :
    t ∉ Subgroup.normalizer ((conjSub t⁻¹ K : Subgroup G) : Set G) := by
  intro hmem
  have h1 : conjSub t (conjSub t⁻¹ K) = conjSub t⁻¹ K := A38.map_conj_eq_iff.mpr hmem
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at h1
  apply htK
  have h2 : conjSub t⁻¹ K = K := h1.symm
  have h3 : t⁻¹ ∈ Subgroup.normalizer (K : Set G) := A38.map_conj_eq_iff.mp h2
  exact (Subgroup.inv_mem_iff _).mp h3

theorem sq_mem_normalizer_conjSub {t : G} {K : Subgroup G}
    (hsq : t * t ∈ Subgroup.normalizer (K : Set G)) :
    t * t ∈ Subgroup.normalizer ((conjSub t⁻¹ K : Subgroup G) : Set G) := by
  apply A38.map_conj_eq_iff.mp
  show conjSub (t * t) (conjSub t⁻¹ K) = conjSub t⁻¹ K
  rw [← conjSub_mul, mul_inv_cancel_right]
  exact conjSub_eq_conjSub_inv_of_sq hsq

theorem conjClosure_conjSub_ne [Finite G] {K T : Subgroup G} {t : G} (ht : t ∈ T)
    (hK : conjClosure K T ≠ K) : conjClosure (conjSub t⁻¹ K) T ≠ conjSub t⁻¹ K := by
  intro hcon
  rw [conjClosure_conjSub_eq (T.inv_mem ht)] at hcon
  apply hK
  have hle : K ≤ conjSub t⁻¹ K := hcon ▸ le_conjClosure K T
  have hcard : Nat.card ↥(conjSub t⁻¹ K) = Nat.card ↥K :=
    Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective
  have hEq : K = conjSub t⁻¹ K := Subgroup.eq_of_le_of_card_ge hle hcard.le
  rw [hcon, ← hEq]

end ConjFacts

section Param

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def GoodIii (Mp T L : Subgroup (MulAut W)) (V : Subgroup W) (t : MulAut W) : Prop :=
  IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧ commV L ≤ fixV (conjAutSub t L) ∧
    ((ModFiveA Mp L V ∧ FiveShape ↥L) ∨ ModFiveB T L V ∨ (D321Two L ∧ orbSup T V ≠ ⊤) ∨
      D321Three Mp L)

theorem GoodIii.congr_of_conjAutSub {Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {g g' : MulAut W}
    (h2 : conjAutSub g L = conjAutSub g' L) : GoodIii Mp T L V g ↔ GoodIii Mp T L V g' := by
  have h1 : (commV L).map g.toMonoidHom = (commV L).map g'.toMonoidHom := by
    rw [← commV_map_conj_eq, ← commV_map_conj_eq]
    exact congrArg commV h2
  unfold GoodIii
  rw [h1, h2]

theorem goodIii_of_modFiveIii {Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (h : ModFiveIii Mp T L V t) (hne : orbSup T V ≠ ⊤) : GoodIii Mp T L V t :=
  ⟨h.1, h.2.1, by
    rcases h.2.2 with ha | hb | hc | hd
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inl ⟨hc, hne⟩))
    · exact Or.inr (Or.inr (Or.inr hd))⟩

theorem goodIii_of_modFiveIiiAB {Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (h : ModFiveIiiAB Mp T L V t) : GoodIii Mp T L V t :=
  ⟨h.1, h.2.1, by
    rcases h.2.2 with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)⟩

end Param

section Dichotomy

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}
  [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

omit [Finite G] [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] in
theorem conjSub_le_of_mem {X : Subgroup G} (hXH : X ≤ H) {g : G} (hg : g ∈ H) : conjSub g X ≤ H := by
  rintro _ ⟨x, hx, rfl⟩
  exact H.mul_mem (H.mul_mem hg (hXH hx)) (H.inv_mem hg)

omit [Finite G] [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] in
theorem conjSub_conjSub_inv_self (t : G) (K : Subgroup G) : conjSub t (conjSub t⁻¹ K) = K := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

omit [Finite G] [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] in
theorem conjSub_inv_conjSub_inv {t : G} {K : Subgroup G} (hsq : t * t ∈ Subgroup.normalizer (K : Set G)) :
    conjSub t⁻¹ (conjSub t⁻¹ K) = K := by
  rw [← conjSub_mul]
  have h1 : t⁻¹ * t⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
    have := (Subgroup.inv_mem_iff _).mpr hsq
    simpa [mul_inv_rev] using this
  exact A38.map_conj_eq_iff.mpr h1

theorem sq_mem_normalizer_of_not_mem (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hK : conjClosure K T ≠ K) {t : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) : t * t ∈ Subgroup.normalizer (K : Set G) := by
  obtain ⟨-, hdata⟩ := five_group_data h hH hA37 hA38 hK
  obtain ⟨-, -, -, hall⟩ := hdata t ht htK
  have htH : t ∈ H := h.T_le_H ht
  rcases hall (t * t) (H.mul_mem htH htH) with h1 | h1
  · exact h1
  · exfalso
    apply htK
    have e : t⁻¹ * (t * t) = t := by group
    rwa [e] at h1

theorem iii_dichotomy_aux (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {t : G} (ht : t ∈ T)
    (hsq : t * t ∈ Subgroup.normalizer (K : Set G)) (hS : F918FiveIiiS h hIU (T.inv_mem ht)) :
    GoodIii (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
        (subM V₁ (conjClosure I H) I)
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, h.T_le_H (T.inv_mem ht)⟩) ∨
      GoodIii (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H (conjSub t⁻¹ K))
        (subM V₁ (conjClosure I H) I)
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, h.T_le_H (T.inv_mem ht)⟩) := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have htH : t ∈ H := h.T_le_H ht
  have hinvH : t⁻¹ ∈ H := h.T_le_H (T.inv_mem ht)
  have hK''H : conjSub t⁻¹ K ≤ H := conjSub_le_of_mem hKH hinvH
  set a := actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, hinvH⟩ with ha
  have hconj : conjAutSub a (autIH V₁ I H K) = autIH V₁ I H (conjSub t⁻¹ K) :=
    conjAutSub_autIH h hKH hinvH
  have hinv : a⁻¹ = actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, htH⟩ := by
    rw [ha, ← map_inv]
    congr 1
    exact Subtype.ext (inv_inv t)
  have hpar : conjAutSub (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, htH⟩)
      (autIH V₁ I H (conjSub t⁻¹ K)) = conjAutSub a (autIH V₁ I H (conjSub t⁻¹ K)) := by
    rw [conjAutSub_autIH h hK''H htH, ha, conjAutSub_autIH h hK''H hinvH,
      conjSub_conjSub_inv_self, conjSub_inv_conjSub_inv hsq]
  have conv : GoodIii (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (conjAutSub a (autIH V₁ I H K))
      (subM V₁ (conjClosure I H) I) a⁻¹ →
      GoodIii (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H (conjSub t⁻¹ K))
        (subM V₁ (conjClosure I H) I) a := by
    intro hG
    rw [hconj, hinv] at hG
    exact (GoodIii.congr_of_conjAutSub hpar).mp hG
  obtain ⟨hF, hflag⟩ := hS
  rcases hflag with hne | hAB1 | hAB2
  · rcases hF with hA1 | hA2
    · exact Or.inl (goodIii_of_modFiveIii hA1 hne)
    · exact Or.inr (conv (goodIii_of_modFiveIii hA2 hne))
  · exact Or.inl (goodIii_of_modFiveIiiAB hAB1)
  · exact Or.inr (conv (goodIii_of_modFiveIiiAB hAB2))

omit [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] in
@[expose] noncomputable def F918Good (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) {t : G} (ht : t ∈ T) : Prop :=
  haveI := factElem h hIU
  GoodIii (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
    (subM V₁ (conjClosure I H) I)
    (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, h.T_le_H (T.inv_mem ht)⟩)

omit [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] in
theorem iii_dichotomy (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {t : G} (ht : t ∈ T)
    (hsq : t * t ∈ Subgroup.normalizer (K : Set G)) (hS : F918FiveIiiS h hIU (T.inv_mem ht)) :
    F918Good h hIU ht ∨ F918Good (hypF918_conj h (T.inv_mem ht)) hIU ht := by
  haveI := factElem h hIU
  have hcc : conjClosure (conjSub t⁻¹ K) T = conjClosure K T := conjClosure_conjSub_eq (T.inv_mem ht)
  have h1 := iii_dichotomy_aux h hIU ht hsq hS
  unfold F918Good
  rw [hcc]
  exact h1

end Dichotomy

section ModuleE

variable {W : Type} [CommGroup W] [Finite W]

theorem fixV_conjAutSub_eq (g : MulAut W) (L : Subgroup (MulAut W)) :
    fixV (conjAutSub g L) = (fixV L).map g.toMonoidHom := by
  ext w
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hw x hx
    have h1 := hw (g * x * g⁻¹) ⟨x, hx, rfl⟩
    have h2 : g (x (g.symm w)) = w := by
      simpa [MulAut.mul_apply] using h1
    have h3 : x (g.symm w) = g.symm w := by
      apply g.injective
      rw [h2]
      simp
    exact h3
  · intro hw y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h1 := hw x hx
    show (g * x * g⁻¹) w = w
    simp only [MulAut.mul_apply]
    have : g⁻¹ w = g.symm w := rfl
    rw [this, h1]
    simp

theorem apply_mem_fixV_of_mem_normalizer {Mp : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (Mp : Set (MulAut W))) {c : W} (hc : c ∈ fixV Mp) : g c ∈ fixV Mp := by
  intro x hx
  have hy : g⁻¹ * x * g ∈ Mp := by
    refine (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr ?_
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]
    exact hx
  have h1 := hc (g⁻¹ * x * g) hy
  have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  calc x (g c) = (g * (g⁻¹ * x * g) * g⁻¹) (g c) := by rw [← e]
    _ = g ((g⁻¹ * x * g) c) := by simp [MulAut.mul_apply]
    _ = g c := by rw [h1]

theorem fixV_conj_le_commV {Mp L : Subgroup (MulAut W)} {g : MulAut W}
    (hMp : Mp = L ⊔ conjAutSub g L) (hg : g ∈ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hsum : IsSumMod (fixV Mp) (commV L) ((commV L).map g.toMonoidHom) ⊤)
    (hincl : commV L ≤ fixV (conjAutSub g L)) (hfix : fixV Mp ≤ commV L) :
    fixV (conjAutSub g L) ≤ commV L := by
  intro w hw
  obtain ⟨hTot, -⟩ := hsum
  have hw' : w ∈ commV L ⊔ (commV L).map g.toMonoidHom ⊔ fixV Mp := hTot ▸ Subgroup.mem_top w
  obtain ⟨y, hy, c, hc, rfl⟩ := Subgroup.mem_sup.mp hw'
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hy
  have hcLg : c ∈ fixV (conjAutSub g L) := by
    have : fixV Mp ≤ fixV (conjAutSub g L) := by
      rw [hMp, CFSG.Quasithin.FixVLat.fixV_sup_eq]
      exact inf_le_right
    exact this hc
  have hbLg : b ∈ fixV (conjAutSub g L) := by
    have h1 : b = (a * b * c) * (a * c)⁻¹ := by
      rw [eq_comm, mul_inv_eq_iff_eq_mul]
      ac_rfl
    rw [h1]
    exact (fixV (conjAutSub g L)).mul_mem hw ((fixV (conjAutSub g L)).inv_mem
      ((fixV (conjAutSub g L)).mul_mem (hincl ha) hcLg))
  obtain ⟨b', hb'A, rfl⟩ := hb
  have h1 : b' ∈ fixV L := by
    intro x hx
    have := hbLg (g * x * g⁻¹) ⟨x, hx, rfl⟩
    have h2 : g (x b') = g b' := by
      simpa [MulAut.mul_apply] using this
    exact g.injective h2
  have h2 : b' ∈ fixV (conjAutSub g L) := hincl hb'A
  have h3 : b' ∈ fixV Mp := by
    rw [hMp, CFSG.Quasithin.FixVLat.fixV_sup_eq]
    exact ⟨h1, h2⟩
  have h4 : g b' ∈ fixV Mp := apply_mem_fixV_of_mem_normalizer hg h3
  exact (commV L).mul_mem ((commV L).mul_mem ha (hfix h4)) (hfix hc)

theorem fixV_eq_bot_of_inf_eq_bot {Mp L : Subgroup (MulAut W)} {g : MulAut W}
    (hMp : Mp = L ⊔ conjAutSub g L) (hLL : conjAutSub g (conjAutSub g L) = L)
    (hincl : commV L ≤ fixV (conjAutSub g L)) (hcomm : commV Mp = ⊤)
    (hα : commV L ⊓ fixV L = ⊥) : fixV Mp = ⊥ := by
  have hB : (commV L).map g.toMonoidHom ≤ fixV L := by
    rintro _ ⟨a, ha, rfl⟩
    intro x hx
    have hx' : x ∈ conjAutSub g (conjAutSub g L) := by rw [hLL]; exact hx
    obtain ⟨y, hy, rfl⟩ := hx'
    have h1 := hincl ha y hy
    show ((g * y * g⁻¹) (g a)) = g a
    simp only [MulAut.mul_apply]
    have e : g⁻¹ (g a) = a := by simp
    rw [e, h1]
  have hB' : (commV L).map g.toMonoidHom ⊓ fixV (conjAutSub g L) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨a, ha, rfl⟩, hfix⟩
    have h1 : a ∈ fixV L := by
      have hfix' : g a ∈ (fixV L).map g.toMonoidHom := by
        rw [← fixV_conjAutSub_eq]
        exact hfix
      obtain ⟨a'', ha'', hga⟩ := hfix'
      have : a'' = a := g.injective hga
      rw [← this]
      exact ha''
    have h2 : a ∈ commV L ⊓ fixV L := ⟨ha, h1⟩
    rw [hα, Subgroup.mem_bot] at h2
    rw [Subgroup.mem_bot]
    show g a = 1
    rw [h2, map_one]
  rw [eq_bot_iff]
  intro c hc
  have hcA : c ∈ commV L ⊔ (commV L).map g.toMonoidHom := by
    have h1 : c ∈ commV Mp := hcomm ▸ Subgroup.mem_top c
    have hc2 : commV (conjAutSub g L) = (commV L).map g.toMonoidHom := commV_map_conj_eq L g
    have h2 : commV Mp ≤ commV L ⊔ (commV L).map g.toMonoidHom := by
      rw [hMp, ← hc2]
      exact CFSG.Quasithin.FixVLat.commV_sup_le _ _
    exact h2 h1
  obtain ⟨a', ha', b', hb', rfl⟩ := Subgroup.mem_sup.mp hcA
  have hcL : a' * b' ∈ fixV L := by
    have : fixV Mp ≤ fixV L := by
      rw [hMp, CFSG.Quasithin.FixVLat.fixV_sup_eq]
      exact inf_le_left
    exact this hc
  have hcLg : a' * b' ∈ fixV (conjAutSub g L) := by
    have : fixV Mp ≤ fixV (conjAutSub g L) := by
      rw [hMp, CFSG.Quasithin.FixVLat.fixV_sup_eq]
      exact inf_le_right
    exact this hc
  have ha'L : a' ∈ fixV L := by
    intro x hx
    have h1 := hcL x hx
    have h2 := hB hb' x hx
    rw [map_mul, h2] at h1
    exact mul_right_cancel h1
  have ha'1 : a' = 1 := by
    have h2 : a' ∈ commV L ⊓ fixV L := ⟨ha', ha'L⟩
    rw [hα, Subgroup.mem_bot] at h2
    exact h2
  have hb'Lg : b' ∈ fixV (conjAutSub g L) := by
    intro y hy
    have h1 := hcLg y hy
    have h2 := hincl ha' y hy
    rw [map_mul, h2] at h1
    exact mul_left_cancel h1
  have hb'1 : b' = 1 := by
    have h2 : b' ∈ (commV L).map g.toMonoidHom ⊓ fixV (conjAutSub g L) := ⟨hb', hb'Lg⟩
    rw [hB', Subgroup.mem_bot] at h2
    exact h2
  rw [ha'1, hb'1, mul_one]
  exact Subgroup.one_mem _

end ModuleE

section CaseC2

variable {W : Type} [CommGroup W] [Finite W]

theorem eq_zero_of_fixed_statedSL_three {m : ℕ} (X : Matrix (Fin 3) (Fin m) (ZMod 2))
    (hX : ∀ γ : ↥(StatedSL 3 (ZMod 2)),
      ((γ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X = X) :
    X = 0 := by
  ext j c
  obtain ⟨i, hij⟩ : ∃ i : Fin 3, i ≠ j := by
    by_cases h0 : j = 0
    · exact ⟨1, by rw [h0]; decide⟩
    · exact ⟨0, fun h => h0 h.symm⟩
  let g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    Matrix.GeneralLinearGroup.mk'' (Matrix.transvection i j 1)
      (by simp [Matrix.det_transvection_of_ne i j hij])
  have h1 := hX ⟨g, CFSG.Open.StatedAPI.mem_statedSL_zmod_two g⟩
  have h2 := congrFun (congrFun h1 i) c
  have h3 : ((((⟨g, CFSG.Open.StatedAPI.mem_statedSL_zmod_two g⟩ : ↥(StatedSL 3 (ZMod 2))) :
      Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X) i c =
      X i c + X j c := by
    show (Matrix.transvection i j (1 : ZMod 2) * X) i c = _
    rw [Matrix.transvection_mul_apply_same]
    simp
  rw [h3] at h2
  have h4 : X j c = 0 := by
    have := h2
    exact add_eq_left.mp this
  simpa using h4

theorem d321Two_realizes {L : Subgroup (MulAut W)} (h : D321Two L) :
    ∃ π : ↥(StatedSL 3 (ZMod 2)) →* ↥L,
      (multiNatModelU 3 4 (ZMod 2)).RealizesVia L (commV L) ⊥ π := by
  obtain ⟨-, I', π, -, hind, hsup, hreal⟩ := h
  have hind' : ∀ i, I' i ⊓ ⨆ (j : Fin 4) (_ : j ≠ i), I' j = ⊥ := fun i => by
    simpa only [bot_sup_eq] using hind i
  have hU : ⨆ i, I' i = commV L := by
    simpa only [bot_sup_eq] using hsup
  exact ⟨π, realizesVia_multiNatModelU (n := 3) (m := 4) (F := ZMod 2) I' π hind' hU
    (hreal 0).1 hreal⟩

theorem exists_coord_of_realizesVia_multi {n m : ℕ} {F : Type} [Field F] {L : Subgroup (MulAut W)}
    {U : Subgroup W} (π : ↥(StatedSL n F) →* ↥L)
    (hreal : (multiNatModelU n m F).RealizesVia L U ⊥ π) :
    ∃ b : ↥U ≃* Multiplicative (Matrix (Fin n) (Fin m) F),
      ∀ (γ : ↥(StatedSL n F)) (u : ↥U) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ U),
        b ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ =
          Multiplicative.ofAdd (((γ : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            Multiplicative.toAdd (b u)) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hreal
  let q := topBotQuotEquiv (Multiplicative (Matrix (Fin n) (Fin m) F))
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let b0 : ↥U →* Multiplicative (Matrix (Fin n) (Fin m) F) := q.toMonoidHom.comp β
  refine ⟨MulEquiv.ofBijective b0 ⟨q.injective.comp hβinj, q.surjective.comp hβs⟩, ?_⟩
  intro γ u hu
  show b0 ⟨_, hu⟩ = Multiplicative.ofAdd (_ * Multiplicative.toAdd (b0 u))
  have hum : β u = QuotientGroup.mk
      (⟨b0 u, trivial⟩ : ↥(⊤ : Subgroup (Multiplicative (Matrix (Fin n) (Fin m) F)))) := by
    apply q.injective
    rfl
  exact congrArg q (hβe γ u ⟨b0 u, trivial⟩ hu trivial hum)

theorem d321Two_commV_inf_fixV {L : Subgroup (MulAut W)} (h : D321Two L) : commV L ⊓ fixV L = ⊥ := by
  obtain ⟨π, hπ⟩ := d321Two_realizes h
  obtain ⟨b, hb⟩ := exists_coord_of_realizesVia_multi π hπ
  rw [eq_bot_iff]
  rintro v ⟨hv, hvf⟩
  rw [Subgroup.mem_bot]
  let u : ↥(commV L) := ⟨v, hv⟩
  have hfix : ∀ γ : ↥(StatedSL 3 (ZMod 2)),
      ((γ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        Multiplicative.toAdd (b u) = Multiplicative.toAdd (b u) := by
    intro γ
    have hγ : ((π γ : ↥L) : MulAut W) v = v := hvf _ (π γ).2
    have h1 := hb γ u (by rw [show (u : W) = v from rfl, hγ]; exact hv)
    have h2 : (⟨((π γ : ↥L) : MulAut W) (u : W), by rw [show (u : W) = v from rfl, hγ]; exact hv⟩ :
        ↥(commV L)) = u := Subtype.ext hγ
    rw [h2] at h1
    exact (congrArg Multiplicative.toAdd h1).symm
  have hX : Multiplicative.toAdd (b u) = 0 := eq_zero_of_fixed_statedSL_three _ hfix
  have h3 : b u = 1 := Multiplicative.toAdd.injective (by rw [hX]; rfl)
  have h4 : u = 1 := b.injective (by rw [h3, map_one])
  exact congrArg Subtype.val h4

end CaseC2

section CaseB2

variable {W : Type} [CommGroup W] [Finite W]

theorem not_commutative_of_isPSL_three {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    ¬ ∀ a b : X, a * b = b * a := by
  intro hc
  haveI : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 1 h).2
  letI : CommGroup X := { ‹Group X› with mul_comm := hc }
  have hp := IsSimpleGroup.prime_card (α := X)
  rw [card_eq_of_isPSL_three_two h] at hp
  norm_num at hp

theorem commutative_of_commV_le_fixV {L : Subgroup (MulAut W)} (h : commV L ≤ fixV L) :
    ∀ a b : ↥L, a * b = b * a := by
  intro a b
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  have ha : ((a : MulAut W) w) * w⁻¹ ∈ commV L := Subgroup.subset_closure ⟨a, a.2, w, rfl⟩
  have hb : ((b : MulAut W) w) * w⁻¹ ∈ commV L := Subgroup.subset_closure ⟨b, b.2, w, rfl⟩
  have h1 : (a : MulAut W) (((b : MulAut W) w) * w⁻¹) = ((b : MulAut W) w) * w⁻¹ := h hb a a.2
  have h2 : (b : MulAut W) (((a : MulAut W) w) * w⁻¹) = ((a : MulAut W) w) * w⁻¹ := h ha b b.2
  show (a : MulAut W) ((b : MulAut W) w) = (b : MulAut W) ((a : MulAut W) w)
  have e1 : (b : MulAut W) w = (((b : MulAut W) w) * w⁻¹) * w := by simp
  have e2 : (a : MulAut W) w = (((a : MulAut W) w) * w⁻¹) * w := by simp
  calc (a : MulAut W) ((b : MulAut W) w)
      = (a : MulAut W) ((((b : MulAut W) w) * w⁻¹) * w) := by rw [← e1]
    _ = (a : MulAut W) (((b : MulAut W) w) * w⁻¹) * (a : MulAut W) w := map_mul _ _ _
    _ = (((b : MulAut W) w) * w⁻¹) * (a : MulAut W) w := by rw [h1]
    _ = (((a : MulAut W) w) * w⁻¹) * (b : MulAut W) w := by ac_rfl
    _ = (b : MulAut W) (((a : MulAut W) w) * w⁻¹) * (b : MulAut W) w := by rw [h2]
    _ = (b : MulAut W) ((((a : MulAut W) w) * w⁻¹) * w) := (map_mul _ _ _).symm
    _ = (b : MulAut W) ((a : MulAut W) w) := by rw [← e2]

theorem fixed_dichotomy_seven {g : MulAut W} (hg : g ^ 7 = 1) {V : Subgroup W} (hV : Nat.card ↥V = 8)
    (hgV : ∀ v ∈ V, g v ∈ V) :
    (∀ v ∈ V, g v = v) ∨ ∀ x ∈ V, g x = x → x = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨v, hvV, hgv⟩, x, hxV, hgx, hx1⟩ := hcon
  haveI : Fintype ↥V := Fintype.ofFinite _
  let f : Function.End ↥V := fun u => ⟨g u, hgV u u.2⟩
  have key : ∀ n : ℕ, ∀ u : ↥V, ((f ^ n) u : W) = (g ^ n) (u : W) := by
    intro n
    induction n with
    | zero => intro u; rw [pow_zero, pow_zero]; rfl
    | succ n ih =>
      intro u
      rw [pow_succ']
      show g (((f ^ n) u : ↥V) : W) = (g ^ (n + 1)) (u : W)
      rw [ih, pow_succ']
      rfl
  have hf : f ^ 7 = 1 := by
    funext u
    apply Subtype.ext
    rw [key 7, hg]
    rfl
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 7) (n := 1) (f := f) (by simpa using hf)
  have hcardV : Fintype.card ↥V = 8 := by rw [← Nat.card_eq_fintype_card]; exact hV
  set S : Set ↥V := Function.fixedPoints f with hS
  have hmem : ∀ u : ↥V, u ∈ S ↔ g (u : W) = u := fun u => by
    rw [hS, Function.mem_fixedPoints_iff]
    exact Subtype.ext_iff
  have h1 : (1 : ↥V) ∈ S := (hmem 1).mpr (map_one g)
  have hx' : (⟨x, hxV⟩ : ↥V) ∈ S := (hmem _).mpr hgx
  have hv' : (⟨v, hvV⟩ : ↥V) ∉ S := fun hh => hgv ((hmem _).mp hh)
  have hne : (1 : ↥V) ≠ ⟨x, hxV⟩ := fun hh => hx1 (congrArg Subtype.val hh).symm
  have hlow : 2 ≤ S.ncard := by
    have := Set.ncard_le_ncard (s := ({1, ⟨x, hxV⟩} : Set ↥V)) (t := S)
      (by
        intro u hu
        rcases hu with rfl | rfl
        · exact h1
        · exact hx') (Set.toFinite _)
    rwa [Set.ncard_pair hne] at this
  have hup : S.ncard ≤ 7 := by
    have hsub : S ⊆ (Set.univ : Set ↥V) \ {⟨v, hvV⟩} := by
      intro u hu
      refine ⟨Set.mem_univ u, fun hh => hv' ?_⟩
      rw [Set.mem_singleton_iff] at hh
      rw [← hh]
      exact hu
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
      Nat.card_eq_fintype_card, hcardV] at this
    omega
  have hcard : Fintype.card ↥S = S.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [hcardV, hcard] at hmod
  unfold Nat.ModEq at hmod
  omega

theorem modFiveB_commV_inf_fixV {T L : Subgroup (MulAut W)} {V : Subgroup W} (hB : ModFiveB T L V)
    (hLV : L ≤ stabSub V) : commV L ⊓ fixV L = ⊥ := by
  obtain ⟨hPSL, ⟨s₀, hs₀T, hs₀N, hs₀V⟩, hdir, hcard⟩ := hB
  obtain ⟨hsup, hinf⟩ := hdir s₀ hs₀T hs₀N hs₀V
  have hLsV : ∀ l ∈ L, ∀ v ∈ V, l v ∈ V := fun l hl v hv => ((hLV hl) v).mpr hv
  have hconj : ∀ l ∈ L, s₀⁻¹ * l * s₀ ∈ L := by
    intro l hl
    refine (Subgroup.mem_normalizer_iff.mp hs₀N (s₀⁻¹ * l * s₀)).mpr ?_
    have e : s₀ * (s₀⁻¹ * l * s₀) * s₀⁻¹ = l := by group
    rw [e]
    exact hl
  have hLVs : ∀ l ∈ L, ∀ b ∈ V.map s₀.toMonoidHom, l b ∈ V.map s₀.toMonoidHom := by
    rintro l hl _ ⟨v, hv, rfl⟩
    refine ⟨(s₀⁻¹ * l * s₀) v, hLsV _ (hconj l hl) v hv, ?_⟩
    show s₀ ((s₀⁻¹ * l * s₀) v) = l (s₀ v)
    simp [MulAut.mul_apply]
  have hV0 : V ⊓ fixV L = ⊥ := by
    haveI : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hPSL).2
    have h168 : Nat.card ↥L = 168 := card_eq_of_isPSL_three_two hPSL
    haveI : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [h168]; norm_num)
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨g, hg7⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 7 (by rw [h168]; norm_num)
    have hgpow : ((g : MulAut W)) ^ 7 = 1 := by
      have h1 : g ^ 7 = 1 := hg7 ▸ pow_orderOf_eq_one g
      rw [← Subgroup.coe_pow, h1]
      rfl
    rcases fixed_dichotomy_seven hgpow hcard (fun v hv => hLsV g g.2 v hv) with hall | hfix1
    · exfalso
      let Sk : Subgroup ↥L :=
        { carrier := {l | ∀ v ∈ V, (l : MulAut W) v = v}
          one_mem' := fun v _ => rfl
          mul_mem' := by
            intro a b ha hb v hv
            show (a : MulAut W) ((b : MulAut W) v) = v
            rw [hb v hv, ha v hv]
          inv_mem' := by
            intro a ha v hv
            show ((a : MulAut W)⁻¹) v = v
            calc ((a : MulAut W)⁻¹) v = ((a : MulAut W)⁻¹) ((a : MulAut W) v) := by rw [ha v hv]
              _ = v := by simp }
      haveI : Sk.Normal :=
        ⟨fun l hl x v hv => by
          have h1 : ((x⁻¹ : ↥L) : MulAut W) v ∈ V := hLsV _ (x⁻¹).2 v hv
          show (x : MulAut W) ((l : MulAut W) (((x⁻¹ : ↥L) : MulAut W) v)) = v
          rw [hl _ h1]
          show (x : MulAut W) (((x : MulAut W)⁻¹) v) = v
          simp⟩
      have hg1 : g ≠ 1 := fun h => by
        rw [h, orderOf_one] at hg7
        norm_num at hg7
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Sk with hbot | htop
      · have : g ∈ (⊥ : Subgroup ↥L) := hbot ▸ hall
        exact hg1 (Subgroup.mem_bot.mp this)
      · have hLfix : ∀ l ∈ L, ∀ v ∈ V, l v = v := fun l hl v hv => by
          have : (⟨l, hl⟩ : ↥L) ∈ Sk := htop ▸ Subgroup.mem_top _
          exact this v hv
        have hle : commV L ≤ fixV L := by
          rw [← hsup]
          refine sup_le (fun v hv l hl => hLfix l hl v hv) ?_
          rintro _ ⟨v, hv, rfl⟩ l hl
          have h1 := hLfix _ (hconj l hl) v hv
          show l (s₀ v) = s₀ v
          have h2 : l (s₀ v) = s₀ ((s₀⁻¹ * l * s₀) v) := by simp [MulAut.mul_apply]
          rw [h2, h1]
        exact not_commutative_of_isPSL_three hPSL (commutative_of_commV_le_fixV hle)
    · rw [eq_bot_iff]
      rintro x ⟨hxV, hxf⟩
      exact Subgroup.mem_bot.mpr (hfix1 x hxV (hxf g g.2))
  rw [eq_bot_iff]
  rintro x ⟨hxA, hxf⟩
  rw [← hsup] at hxA
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hxA
  have hab : ∀ l ∈ L, l a = a ∧ l b = b := by
    intro l hl
    have h1 : l (a * b) = a * b := hxf l hl
    rw [map_mul] at h1
    have h2 : (l a) * a⁻¹ ∈ V := V.mul_mem (hLsV l hl a ha) (V.inv_mem ha)
    have h3 : b * (l b)⁻¹ ∈ V.map s₀.toMonoidHom :=
      (V.map s₀.toMonoidHom).mul_mem hb ((V.map s₀.toMonoidHom).inv_mem (hLVs l hl b hb))
    have h4 : (l a) * a⁻¹ = b * (l b)⁻¹ := by
      have e : l a = (a * b) * (l b)⁻¹ := eq_mul_inv_of_mul_eq h1
      rw [mul_inv_eq_iff_eq_mul, e]
      ac_rfl
    have h5 : (l a) * a⁻¹ ∈ V ⊓ V.map s₀.toMonoidHom := ⟨h2, h4 ▸ h3⟩
    rw [hinf, Subgroup.mem_bot] at h5
    have h6 : l a = a := mul_inv_eq_one.mp h5
    exact ⟨h6, by rw [h6] at h1; exact mul_left_cancel h1⟩
  have ha1 : a = 1 := by
    have h2 : a ∈ V ⊓ fixV L := ⟨ha, fun l hl => (hab l hl).1⟩
    rw [hV0, Subgroup.mem_bot] at h2
    exact h2
  obtain ⟨b', hb', rfl⟩ := hb
  have hb'1 : b' = 1 := by
    have h2 : b' ∈ V ⊓ fixV L := ⟨hb', fun l hl => by
      have hl₁ : s₀ * l * s₀⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hs₀N l).mp hl
      have h3 := (hab _ hl₁).2
      have h6 : s₀ (l b') = s₀ b' := by
        simpa [MulAut.mul_apply] using h3
      exact s₀.injective h6⟩
    rw [hV0, Subgroup.mem_bot] at h2
    exact h2
  rw [ha1, hb'1]
  show (1 : W) * s₀ 1 ∈ (⊥ : Subgroup W)
  simp

end CaseB2

section Eq

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}
  [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem commV_autIH_conjClosure_eq_top (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hIrr : IsIrrPlusTilde V₁ (conjClosure K T) I) :
    commV (autIH V₁ I H (conjClosure K T)) = ⊤ := by
  rw [commV_autIH_eq_subM h hIU h.K₀_le_H]
  show (tildeOf V₁ ⁅conjClosure I H, conjClosure K T⁆).subgroupOf (tildeOf V₁ (conjClosure I H)) = ⊤
  rw [HypF918.tilde_commutator_conjClosure h hIU hIrr]
  exact Subgroup.subgroupOf_self _

theorem tilde_eq_of_fixV_le (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {t : G}
    (htH : t ∈ H)
    (hincl : tildeOf V₁ ⁅conjClosure I H, K⁆ ≤ tildeOf V₁ (conjClosure I H) ⊓
      Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K) : Set (GtOf V₁)))
    (hle : fixV (conjAutSub
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, H.inv_mem htH⟩)
        (autIH V₁ I H K)) ≤ commV (autIH V₁ I H K)) :
    tildeOf V₁ ⁅conjClosure I H, K⁆ = tildeOf V₁ (conjClosure I H) ⊓
      Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K) : Set (GtOf V₁)) := by
  refine le_antisymm hincl ?_
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hKtH : conjSub t⁻¹ K ≤ H := conjSub_le_of_mem hKH (H.inv_mem htH)
  rintro y ⟨hyI, hyC⟩
  let w : ↥(tildeOf V₁ (conjClosure I H)) := ⟨y, hyI⟩
  have hw : w ∈ fixV (autIH V₁ I H (conjSub t⁻¹ K)) := by
    rw [fixV_autIH_eq hIU hKtH]
    exact Subgroup.mem_subgroupOf.mpr hyC
  rw [← conjAutSub_autIH h hKH (H.inv_mem htH)] at hw
  have hw' := hle hw
  rw [← map_commV_autIH h hIU hKH]
  exact ⟨w, hw', rfl⟩

theorem five_iii_eq_of_fixed (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hK : conjClosure K T ≠ K) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) {t : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) (hsq : t * t ∈ Subgroup.normalizer (K : Set G))
    (hG : GoodIii (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
        (subM V₁ (conjClosure I H) I)
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, h.T_le_H (T.inv_mem ht)⟩))
    (hfix : fixV (autIH V₁ I H (conjClosure K T)) ≤ commV (autIH V₁ I H K)) :
    tildeOf V₁ ⁅conjClosure I H, K⁆ = tildeOf V₁ (conjClosure I H) ⊓
      Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K) : Set (GtOf V₁)) := by
  have hinvT : t⁻¹ ∈ T := T.inv_mem ht
  have hinvH : t⁻¹ ∈ H := h.T_le_H hinvT
  have htH : t ∈ H := h.T_le_H ht
  have hinvK : t⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun hh => htK ((Subgroup.inv_mem_iff _).mp hh)
  obtain ⟨hsum, hincl, -⟩ := hG
  obtain ⟨-, -, hdata⟩ := five_prelim h hH hK hIU hnt hA37 hA38
  obtain ⟨-, -, hMp, -⟩ := hdata t⁻¹ hinvT hinvK
  have hgN : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, hinvH⟩ ∈
      Subgroup.normalizer ((autIH V₁ I H (conjClosure K T) : Subgroup _) : Set _) :=
    actH_mem_normalizer_autIH h h.K₀_le_H hinvH (h.K₀_normal hinvH)
  have hle := fixV_conj_le_commV hMp hgN hsum hincl hfix
  exact tilde_eq_of_fixV_le h hIU htH (tilde_commutator_le_centralizer h hIU htH hincl) hle

theorem five_iii_eq_of_inf (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hK : conjClosure K T ≠ K) (hIU : I ≤ conjClosure Vp H)
    (hIrr : IsIrrPlusTilde V₁ (conjClosure K T) I)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) {t : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) (hsq : t * t ∈ Subgroup.normalizer (K : Set G))
    (hG : GoodIii (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
        (subM V₁ (conjClosure I H) I)
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, h.T_le_H (T.inv_mem ht)⟩))
    (hα : commV (autIH V₁ I H K) ⊓ fixV (autIH V₁ I H K) = ⊥) :
    tildeOf V₁ ⁅conjClosure I H, K⁆ = tildeOf V₁ (conjClosure I H) ⊓
      Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K) : Set (GtOf V₁)) := by
  have hinvT : t⁻¹ ∈ T := T.inv_mem ht
  have hinvH : t⁻¹ ∈ H := h.T_le_H hinvT
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hinvK : t⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun hh => htK ((Subgroup.inv_mem_iff _).mp hh)
  have hincl := hG.2.1
  obtain ⟨-, -, hdata⟩ := five_prelim h hH hK hIU hnt hA37 hA38
  obtain ⟨-, -, hMp, -⟩ := hdata t⁻¹ hinvT hinvK
  have hLL : conjAutSub (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, hinvH⟩)
      (conjAutSub (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, hinvH⟩)
        (autIH V₁ I H K)) = autIH V₁ I H K := by
    have hK''H : conjSub t⁻¹ K ≤ H := conjSub_le_of_mem hKH hinvH
    rw [conjAutSub_autIH h hKH hinvH, conjAutSub_autIH h hK''H hinvH, conjSub_inv_conjSub_inv hsq]
  have hfix : fixV (autIH V₁ I H (conjClosure K T)) = ⊥ :=
    fixV_eq_bot_of_inf_eq_bot hMp hLL hincl (commV_autIH_conjClosure_eq_top h hIU hIrr) hα
  exact five_iii_eq_of_fixed h hH hA37 hA38 hK hIU hnt ht htK hsq hG (by rw [hfix]; exact bot_le)

end Eq

section Cases

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

@[expose] noncomputable def F918IiiD (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) : Prop :=
  haveI := factElem h hIU
  D321Three (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H K)

end Cases

end CFSG.Quasithin.RonanF918
