module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShapes
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapCoverF4
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPBarDown

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def BorelRankTwoTop (M : Type) [Group M] : Prop :=
  ∀ S : Subgroup M, IsSylowIn 2 S (⊤ : Subgroup M) →
    ∃ P₁ P₂ : Subgroup M, P₁ < ⊤ ∧ P₂ < ⊤ ∧ (∀ Q : Subgroup M, P₁ < Q → Q = ⊤) ∧
      (∀ Q : Subgroup M, P₂ < Q → Q = ⊤) ∧
      normalizer (S : Set M) ≤ P₁ ∧ normalizer (S : Set M) ≤ P₂ ∧
      (∀ g : M, conjSubgroup P₁ g ≠ P₂) ∧
      ∀ P : Subgroup M, normalizer (S : Set M) ≤ P →
        P = normalizer (S : Set M) ∨ P = P₁ ∨ P = P₂ ∨ P = ⊤

private theorem wccb3_barSub_mono {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {Q : Type} [Group Q] {φ : ↥H →* Q} {A B : Subgroup G} (hAB : A ≤ B) :
    barSub H φ A ≤ barSub H φ B :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono H hAB)

private theorem wccb3_barPre_mono {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {Q : Type} [Group Q] {φ : ↥H →* Q} {A B : Subgroup Q} (hAB : A ≤ B) :
    barPre H φ A ≤ barPre H φ B := by
  intro g hg
  obtain ⟨hgH, hgA⟩ := mem_barPre.mp hg
  exact mem_barPre.mpr ⟨hgH, hAB hgA⟩

private theorem wccb3_barPre_lt {G : Type} [Group G] [Finite G] {H C : Subgroup G}
    {Q : Type} [Group Q] {φ : ↥H →* Q} (hφ : IsBarMap H C φ) {A B : Subgroup Q} :
    barPre H φ A < barPre H φ B ↔ A < B := by
  constructor
  · intro h
    have hle : A ≤ B := by
      have h' := wccb3_barSub_mono (φ := φ) h.le
      rwa [barSub_barPre hφ A, barSub_barPre hφ B] at h'
    exact lt_of_le_of_ne hle fun heq => h.ne (by rw [heq])
  · intro h
    exact lt_of_le_of_ne (wccb3_barPre_mono h.le) fun heq => h.ne (by
      have h' := congrArg (barSub H φ) heq
      rwa [barSub_barPre hφ A, barSub_barPre hφ B] at h')

private theorem wccb3_center_map_le_centralizer {Y : Type} [Group Y] {L S : Subgroup Y}
    (hSL : S ≤ L) :
    (Subgroup.center ↥L).map L.subtype ≤ Subgroup.centralizer (S : Set Y) := by
  intro z hz
  obtain ⟨k, hkZ, rfl⟩ := Subgroup.mem_map.mp hz
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hkZ ⟨s, hSL hs⟩)

private theorem wccb3_isMaxParabolicMod_barPre {G : Type} [Group G] [Finite G]
    {L S C : Subgroup G} {Q : Type} [Group Q] {φ : ↥L →* Q}
    (hCL : C ≤ L) (hφ : IsBarMap L C φ) (hSL : S ≤ L) (hS2 : IsPGroup 2 S)
    (hSodd : ¬ 2 ∣ S.relIndex L)
    (hCB : C ≤ L ⊓ Subgroup.normalizer (S : Set G))
    (hbarB : barSub L φ (L ⊓ Subgroup.normalizer (S : Set G)) =
      Subgroup.normalizer (((S.subgroupOf L).map φ) : Set Q))
    {Pbar : Subgroup Q} (hPlt : Pbar < ⊤) (hPmax : ∀ R : Subgroup Q, Pbar < R → R = ⊤)
    (hNS : Subgroup.normalizer (((S.subgroupOf L).map φ) : Set Q) ≤ Pbar) :
    IsMaxParabolicMod (⊥ : Subgroup G) L (barPre L φ Pbar) := by
  have hCPbar : C ≤ barPre L φ Pbar := le_barPre hCL hφ Pbar
  refine ⟨bot_le, ?_, ?_, S, bot_le, hSL, ?_, hSodd, ?_⟩
  · have h := (wccb3_barPre_lt hφ (A := Pbar) (B := ⊤)).mpr hPlt
    rwa [barPre_top] at h
  · intro Y' hPY hY'L
    have hCY' : C ≤ Y' := hCPbar.trans hPY.le
    have hPbar_le : Pbar ≤ barSub L φ Y' := by
      have h' := wccb3_barSub_mono (φ := φ) hPY.le
      rwa [barSub_barPre hφ Pbar] at h'
    have hlt : Pbar < barSub L φ Y' := by
      refine lt_of_le_of_ne hPbar_le ?_
      intro heq
      have h2 : Y' = barPre L φ Pbar := by
        calc Y' = barPre L φ (barSub L φ Y') := (barPre_barSub hφ hCY' hY'L).symm
          _ = barPre L φ Pbar := by rw [heq]
      exact hPY.ne h2.symm
    have htop : barSub L φ Y' = ⊤ := hPmax (barSub L φ Y') hlt
    calc Y' = barPre L φ (barSub L φ Y') := (barPre_barSub hφ hCY' hY'L).symm
      _ = barPre L φ ⊤ := by rw [htop]
      _ = L := barPre_top
  · intro s hs
    obtain ⟨k, hk⟩ := hS2.exists_pow_pow_eq_one ⟨s, hs⟩
    exact ⟨k, Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hk)⟩
  · have hstep : barSub L φ (L ⊓ Subgroup.normalizer (S : Set G)) ≤ Pbar :=
      hbarB.trans_le hNS
    calc L ⊓ Subgroup.normalizer (S : Set G)
        = barPre L φ (barSub L φ (L ⊓ Subgroup.normalizer (S : Set G))) :=
          (barPre_barSub hφ hCB inf_le_left).symm
      _ ≤ barPre L φ Pbar := wccb3_barPre_mono hstep

theorem borelRankTwoOn_of_quotient (Sh : ShapePred)
    (hSh : ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), Sh L → OddShape5 L)
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), Sh L →
      BorelRankTwoTop (↥L ⧸ Subgroup.center ↥L)) :
    BorelRankTwoOn Sh := by
  intro Y _ _ L S hLsh hS
  have hodd : Odd (Nat.card ↥(Subgroup.center ↥L)) := (hSh Y L hLsh).2.1
  let Z : Subgroup ↥L := Subgroup.center ↥L
  let M := ↥L ⧸ Z
  let φ : ↥L →* M := QuotientGroup.mk' Z
  let Sbar : Subgroup M := (S.subgroupOf L).map φ
  let B : Subgroup Y := L ⊓ Subgroup.normalizer (S : Set Y)
  have hφker : φ.ker = Z := QuotientGroup.ker_mk' Z
  have hCL : Z.map L.subtype ≤ L := Subgroup.map_subtype_le Z
  have hφ : IsBarMap L (Z.map L.subtype) φ := by
    refine ⟨QuotientGroup.mk'_surjective Z, ?_⟩
    intro k
    have h1 : φ k = 1 ↔ k ∈ Z := by
      rw [← MonoidHom.mem_ker, hφker]
    rw [h1]
    exact ⟨fun hk => Subgroup.mem_map.mpr ⟨k, hk, rfl⟩, fun hk => by
      obtain ⟨z, hz, hzk⟩ := Subgroup.mem_map.mp hk
      rwa [Subtype.ext hzk] at hz⟩
  have hS1 : IsPGroup 2 (S.subgroupOf L) :=
    hS.isPGroup.comap_of_injective L.subtype L.subtype_injective
  have hSylSbar : IsSylowIn 2 Sbar (⊤ : Subgroup M) := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hS1.map φ
    · rw [Subgroup.relIndex_top_right]
      show ¬ 2 ∣ ((S.subgroupOf L).map φ).index
      rw [Subgroup.index_map, MonoidHom.range_eq_top_of_surjective φ hφ.surjective,
        Subgroup.index_top, mul_one]
      exact fun hdvd => hS.not_dvd_relIndex (hdvd.trans (Subgroup.index_dvd_of_le le_sup_left))
  have hZB : Z.map L.subtype ≤ B := by
    refine le_inf hCL ?_
    exact (wccb3_center_map_le_centralizer hS.le).trans
      (Subgroup.centralizer_le_normalizer (S : Set Y))
  have hBL : B ≤ L := inf_le_left
  have hBbar : barSub L φ B = Subgroup.normalizer (Sbar : Set M) := by
    change ((B.subgroupOf L).map φ) = Subgroup.normalizer (((S.subgroupOf L).map φ) : Set M)
    have h1 : B.subgroupOf L = Subgroup.normalizer (S.subgroupOf L) := by
      change (L ⊓ Subgroup.normalizer (S : Set Y)).comap L.subtype =
        Subgroup.normalizer (S.comap L.subtype)
      rw [Subgroup.comap_inf,
        show L.comap L.subtype = (⊤ : Subgroup ↥L) from Subgroup.subgroupOf_self L, top_inf_eq]
      exact Subgroup.subgroupOf_normalizer_eq hS.le
    rw [h1]
    exact (normalizer_map_of_cover φ hφ.surjective (by rw [hφker])
      (by rw [hφker]; exact hodd) hS1).symm
  obtain ⟨Pbar1, Pbar2, hPbar1lt, hPbar2lt, hPbar1max, hPbar2max, hNS1, hNS2,
    hnonconj, hover⟩ := h Y L hLsh Sbar hSylSbar
  have hB1 : B ≤ barPre L φ Pbar1 := by
    have hstep : barSub L φ B ≤ Pbar1 := hBbar.trans_le hNS1
    calc B = barPre L φ (barSub L φ B) := (barPre_barSub hφ hZB hBL).symm
      _ ≤ barPre L φ Pbar1 := wccb3_barPre_mono hstep
  have hB2 : B ≤ barPre L φ Pbar2 := by
    have hstep : barSub L φ B ≤ Pbar2 := hBbar.trans_le hNS2
    calc B = barPre L φ (barSub L φ B) := (barPre_barSub hφ hZB hBL).symm
      _ ≤ barPre L φ Pbar2 := wccb3_barPre_mono hstep
  refine ⟨barPre L φ Pbar1, barPre L φ Pbar2, ?_, ?_, hB1, hB2, ?_, ?_⟩
  · exact wccb3_isMaxParabolicMod_barPre hCL hφ hS.le hS.isPGroup hS.not_dvd_relIndex
      hZB hBbar hPbar1lt hPbar1max hNS1
  · exact wccb3_isMaxParabolicMod_barPre hCL hφ hS.le hS.isPGroup hS.not_dvd_relIndex
      hZB hBbar hPbar2lt hPbar2max hNS2
  · intro l hl hconj
    apply hnonconj (φ ⟨l, hl⟩)
    have h1 : barSub L φ (conjSubgroup (barPre L φ Pbar1) l) =
        barSub L φ (barPre L φ Pbar2) := by rw [hconj]
    rw [barSub_conjSubgroup φ (barPre L φ Pbar1) ⟨l, hl⟩,
      barSub_barPre hφ Pbar1, barSub_barPre hφ Pbar2] at h1
    exact h1
  · intro P hBP hPL
    have hZP : Z.map L.subtype ≤ P := hZB.trans hBP
    have hPbar : Subgroup.normalizer (Sbar : Set M) ≤ barSub L φ P := by
      rw [← hBbar]
      exact wccb3_barSub_mono hBP
    rcases hover (barSub L φ P) hPbar with h | h | h | h
    · left
      have hh : barSub L φ P = barSub L φ B := h.trans hBbar.symm
      calc P = barPre L φ (barSub L φ P) := (barPre_barSub hφ hZP hPL).symm
        _ = barPre L φ (barSub L φ B) := by rw [hh]
        _ = B := barPre_barSub hφ hZB hBL
    · right; left
      calc P = barPre L φ (barSub L φ P) := (barPre_barSub hφ hZP hPL).symm
        _ = barPre L φ Pbar1 := by rw [h]
    · right; right; left
      calc P = barPre L φ (barSub L φ P) := (barPre_barSub hφ hZP hPL).symm
        _ = barPre L φ Pbar2 := by rw [h]
    · right; right; right
      calc P = barPre L φ (barSub L φ P) := (barPre_barSub hφ hZP hPL).symm
        _ = barPre L φ ⊤ := by rw [h]
        _ = L := barPre_top

end CFSG.LocalAnalysis.WeakClosure81

end
