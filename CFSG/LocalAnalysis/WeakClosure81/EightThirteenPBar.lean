module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreBar
public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G]

section Bar

variable {H C : Subgroup G} {Q : Type} [Group Q] {φ : ↥H →* Q}

private theorem wc813pbar_barPre_mono {A B : Subgroup Q} (hAB : A ≤ B) :
    barPre H φ A ≤ barPre H φ B := fun _ hg =>
  let ⟨hgH, hgA⟩ := mem_barPre.mp hg
  mem_barPre.mpr ⟨hgH, hAB hgA⟩

private theorem wc813pbar_barSub_mono {A B : Subgroup G} (hAB : A ≤ B) :
    barSub H φ A ≤ barSub H φ B := fun _ hx =>
  let ⟨a, haA, hax⟩ := mem_barSub.mp hx
  mem_barSub.mpr ⟨a, hAB haA, hax⟩

private def wc813pbar_proj (H : Subgroup G) {Q : Type} [Group Q] (φ : ↥H →* Q)
    (Xb : Subgroup Q) : ↥(barPre H φ Xb) →* ↥Xb :=
  (φ.comp (Subgroup.inclusion (barPre_le H φ Xb))).codRestrict Xb fun g => by
    obtain ⟨hg, hgX⟩ := mem_barPre.mp g.2
    have h : (Subgroup.inclusion (barPre_le H φ Xb) g : ↥H) = ⟨(g : G), hg⟩ :=
      Subtype.ext rfl
    rw [MonoidHom.comp_apply, h]
    exact hgX

private theorem wc813pbar_proj_apply (H : Subgroup G) {Q : Type} [Group Q] (φ : ↥H →* Q)
    (Xb : Subgroup Q) (g : ↥(barPre H φ Xb)) :
    (wc813pbar_proj H φ Xb g : Q) =
      φ (Subgroup.inclusion (barPre_le H φ Xb) g) := rfl

private theorem wc813pbar_mem_barPre_iff_proj {H : Subgroup G} {Q : Type} [Group Q]
    {φ : ↥H →* Q} {Xb Yb : Subgroup Q} (g : ↥(barPre H φ Yb)) :
    (wc813pbar_proj H φ Yb g : Q) ∈ Xb ↔ (g : G) ∈ barPre H φ Xb := by
  rw [wc813pbar_proj_apply]
  constructor
  · intro h
    exact mem_barPre.mpr ⟨barPre_le H φ Yb g.2, h⟩
  · intro h
    obtain ⟨hg, hgX⟩ := mem_barPre.mp h
    have h' : (Subgroup.inclusion (barPre_le H φ Yb) g : ↥H) = ⟨(g : G), hg⟩ :=
      Subtype.ext rfl
    rwa [h']

private theorem wc813pbar_subgroupOf_barPre_eq_comap_proj {Ab Bb : Subgroup Q}
    (hAB : Ab ≤ Bb) : (barPre H φ Ab).subgroupOf (barPre H φ Bb) =
      (Ab.subgroupOf Bb).comap (wc813pbar_proj H φ Bb) := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  exact (wc813pbar_mem_barPre_iff_proj g).symm

theorem barPre_top : barPre H φ (⊤ : Subgroup Q) = H := by
  ext g
  rw [mem_barPre]
  exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

theorem barPre_bot (hφ : IsBarMap H C φ) (hCH : C ≤ H) : barPre H φ (⊥ : Subgroup Q) = C := by
  ext g
  rw [mem_barPre]
  constructor
  · rintro ⟨hg, hg1⟩
    rw [Subgroup.mem_bot] at hg1
    exact (hφ.ker_iff ⟨g, hg⟩).mp hg1
  · intro hg
    exact ⟨hCH hg, Subgroup.mem_bot.mpr ((hφ.ker_iff ⟨g, hCH hg⟩).mpr hg)⟩

theorem hasQuotShape_barPre (hφ : IsBarMap H C φ) {Lb Nb : Subgroup Q}
    {P : ∀ (X : Type) [Group X], Prop} (h : HasQuotShape Lb (Nb : Set Q) P) :
    HasQuotShape (barPre H φ Lb) ((barPre H φ Nb : Subgroup G) : Set G) P := by
  obtain ⟨X, hX, ψ, hψ, hker, hP⟩ := h
  refine ⟨X, hX, ψ.comp (wc813pbar_proj H φ Lb), ?_, ?_, hP⟩
  · intro x
    obtain ⟨l, hl⟩ := hψ x
    obtain ⟨h, hh⟩ := hφ.surjective l
    have hhL : (h : G) ∈ barPre H φ Lb := mem_barPre.mpr ⟨h.2, by rw [hh]; exact l.2⟩
    refine ⟨⟨h, hhL⟩, ?_⟩
    rw [MonoidHom.comp_apply]
    have hproj : wc813pbar_proj H φ Lb ⟨h, hhL⟩ = l := by
      apply Subtype.ext
      rw [wc813pbar_proj_apply]
      have hincl : Subgroup.inclusion (barPre_le H φ Lb) ⟨h, hhL⟩ = h := Subtype.ext rfl
      rw [hincl]
      exact hh
    rw [hproj, hl]
  · intro k
    rw [MonoidHom.comp_apply, hker (wc813pbar_proj H φ Lb k)]
    exact wc813pbar_mem_barPre_iff_proj k

theorem isSubnormal_barPre {Lb Mb : Subgroup Q} (h : IsSubnormal Lb Mb) :
    IsSubnormal (barPre H φ Lb) (barPre H φ Mb) :=
  CFSG.Open.IsSubnormal.rec
    (motive := fun A B _ => CFSG.Open.IsSubnormal (barPre H φ A) (barPre H φ B))
    (fun _ => CFSG.Open.IsSubnormal.refl _)
    (fun hAM hn _ ih => CFSG.Open.IsSubnormal.step
      (wc813pbar_barPre_mono (φ := φ) hAM)
      (by
        rw [wc813pbar_subgroupOf_barPre_eq_comap_proj (φ := φ) hAM]
        exact hn.comap _) ih)
    h

theorem isComponentModN_barPre (hφ : IsBarMap H C φ) (hCH : C ≤ H) {Lb : Subgroup Q}
    (h : IsComponentModN (⊥ : Subgroup Q) ⊤ Lb) : IsComponentModN C H (barPre H φ Lb) := by
  obtain ⟨-, -, -, hsub, hshape⟩ := h
  refine ⟨?_, le_barPre hCH hφ Lb, barPre_le H φ Lb, ?_, ?_⟩
  · rw [show C.subgroupOf H = φ.ker from ?_]
    exact MonoidHom.normal_ker φ
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact (hφ.ker_iff x).symm
  · have h' := isSubnormal_barPre (φ := φ) hsub
    rwa [barPre_top] at h'
  · have h' := hasQuotShape_barPre hφ hshape
    rwa [barPre_bot hφ hCH] at h'

private theorem wc813pbar_barPre_barSub (hφ : IsBarMap H C φ) {Y : Subgroup G}
    (hCY : C ≤ Y) (hYH : Y ≤ H) : barPre H φ (barSub H φ Y) = Y := by
  ext g
  simp only [mem_barPre, mem_barSub]
  constructor
  · rintro ⟨hg, y, hyY, hyφ⟩
    have hker : ((⟨g, hg⟩ : ↥H) * y⁻¹) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyφ]
      group
    have hC : g * (y : G)⁻¹ ∈ C := by
      have h' := (hφ.ker_iff ((⟨g, hg⟩ : ↥H) * y⁻¹)).mp hker
      simpa using h'
    have hg' : g = (g * (y : G)⁻¹) * (y : G) := by group
    rw [hg']
    exact Y.mul_mem (hCY hC) hyY
  · intro hgY
    exact ⟨hYH hgY, ⟨⟨g, hYH hgY⟩, hgY, rfl⟩⟩

private theorem wc813pbar_comap_barSub (hφ : IsBarMap H C φ) (hCH : C ≤ H) {Y : Subgroup G}
    (hCY : C ≤ Y) (hYH : Y ≤ H) : (barSub H φ Y).comap φ = Y.subgroupOf H := by
  ext x
  rw [Subgroup.mem_comap, mem_barSub, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hyY, hyφ⟩
    have hker : (x * y⁻¹) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyφ]
      group
    have hC : (x : G) * (y : G)⁻¹ ∈ C := by
      have h' := (hφ.ker_iff (x * y⁻¹)).mp hker
      simpa using h'
    have hx' : (x : G) = ((x : G) * (y : G)⁻¹) * (y : G) := by group
    rw [hx']
    exact Y.mul_mem (hCY hC) hyY
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem wc813pbar_relIndex_barPre (hφ : IsBarMap H C φ) (hCH : C ≤ H)
    {Pb : Subgroup Q} {Y : Subgroup G} (hCY : C ≤ Y) (hY : Y ≤ barPre H φ Pb) :
    Y.relIndex (barPre H φ Pb) = (barSub H φ Y).relIndex Pb := by
  have hYH : Y ≤ H := hY.trans (barPre_le H φ Pb)
  have hsub : (barPre H φ Pb).subgroupOf H = Pb.comap φ := by
    change ((Pb.comap φ).map H.subtype).comap H.subtype = Pb.comap φ
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hA : Y.subgroupOf H = (barSub H φ Y).comap φ :=
    (wc813pbar_comap_barSub hφ hCH hCY hYH).symm
  rw [← Subgroup.relIndex_subgroupOf (barPre_le H φ Pb)]
  rw [hA, hsub, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective hφ.surjective Pb]

private theorem wc813pbar_barSub_normalizer_le (φ : ↥H →* Q) {S' : Subgroup G} (hS'H : S' ≤ H) :
    barSub H φ (Subgroup.normalizer (S' : Set G)) ≤
      Subgroup.normalizer ((barSub H φ S' : Subgroup Q) : Set Q) := by
  have h1 : (Subgroup.normalizer (S' : Set G)).subgroupOf H =
      Subgroup.normalizer (S'.subgroupOf H) := Subgroup.subgroupOf_normalizer_eq hS'H
  unfold barSub
  rw [h1]
  exact Subgroup.le_normalizer_map φ

private def wc813pbar_twoSet (N K : Subgroup G) : Set (Subgroup G) :=
  {W | N ≤ W ∧ W ≤ K ∧ (W.subgroupOf K).Normal ∧
    ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k ∈ N}

private theorem wc813pbar_oTwoMod_eq (N K : Subgroup G) :
    oTwoMod N K = ⨆ W ∈ wc813pbar_twoSet N K, W := rfl

private theorem wc813pbar_barSub_mem_twoSet (hφ : IsBarMap H C φ) (hCH : C ≤ H)
    {Kb : Subgroup Q} {W : Subgroup G}
    (hW : W ∈ wc813pbar_twoSet C (barPre H φ Kb)) :
    barSub H φ W ∈ wc813pbar_twoSet (⊥ : Subgroup Q) Kb := by
  obtain ⟨hCW, hWK, hWnorm, hWpow⟩ := hW
  have hbarWK : barSub H φ W ≤ Kb := by
    have h' := wc813pbar_barSub_mono (φ := φ) (H := H) hWK
    rwa [barSub_barPre hφ Kb] at h'
  refine ⟨bot_le, hbarWK, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hbarWK]
    have hKnorm : barPre H φ Kb ≤ Subgroup.normalizer (W : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWK).mp hWnorm
    have h' := barSub_le_normalizer_barSub φ (A := barPre H φ Kb) (B := W) hKnorm
    rwa [barSub_barPre hφ Kb] at h'
  · intro x hx
    obtain ⟨w, hwW, hwx⟩ := mem_barSub.mp hx
    obtain ⟨k, hk⟩ := hWpow (w : G) hwW
    refine ⟨k, ?_⟩
    rw [← hwx, ← map_pow]
    exact Subgroup.mem_bot.mpr ((hφ.ker_iff (w ^ 2 ^ k)).mpr (by simpa using hk))

private theorem wc813pbar_barPre_mem_twoSet (hφ : IsBarMap H C φ) (hCH : C ≤ H)
    {Kb : Subgroup Q} {Wb : Subgroup Q}
    (hWb : Wb ∈ wc813pbar_twoSet (⊥ : Subgroup Q) Kb) :
    barPre H φ Wb ∈ wc813pbar_twoSet C (barPre H φ Kb) := by
  obtain ⟨-, hWbK, hWbnorm, hWbpow⟩ := hWb
  have hle : barPre H φ Wb ≤ barPre H φ Kb := wc813pbar_barPre_mono hWbK
  refine ⟨le_barPre hCH hφ Wb, hle, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    have hKbnorm : Kb ≤ Subgroup.normalizer (Wb : Set Q) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWbK).mp hWbnorm
    have h' := le_normalizer_barPre hφ (A := barPre H φ Kb) (Xb := Wb)
      (barPre_le H φ Kb) (by rwa [barSub_barPre hφ Kb])
    exact h'
  · intro g hg
    obtain ⟨hgH, hgWb⟩ := mem_barPre.mp hg
    obtain ⟨k, hk⟩ := hWbpow (φ ⟨g, hgH⟩) hgWb
    refine ⟨k, ?_⟩
    have hker : φ ((⟨g, hgH⟩ : ↥H) ^ 2 ^ k) = 1 := by
      rw [map_pow, Subgroup.mem_bot.mp hk]
    have h' := (hφ.ker_iff ((⟨g, hgH⟩ : ↥H) ^ 2 ^ k)).mp hker
    simpa using h'

private theorem wc813pbar_comap_iSup {ι : Sort*} (hφ : IsBarMap H C φ) (Xb : ι → Subgroup Q)
    (i0 : ι) (h0 : Xb i0 = ⊥) :
    (⨆ i, Xb i).comap φ = ⨆ i, (Xb i).comap φ := by
  apply le_antisymm
  · have key : ∀ y, y ∈ ⨆ i, Xb i → ∀ x : ↥H, φ x = y → x ∈ ⨆ i, (Xb i).comap φ := by
      intro y hy
      refine Subgroup.iSup_induction Xb
        (C := fun z => ∀ x : ↥H, φ x = z → x ∈ ⨆ i, (Xb i).comap φ) hy ?_ ?_ ?_
      · intro i z hz x hx
        refine Subgroup.mem_iSup_of_mem i ?_
        rw [Subgroup.mem_comap]
        rwa [hx]
      · intro x hx
        refine Subgroup.mem_iSup_of_mem i0 ?_
        rw [h0, Subgroup.mem_comap, Subgroup.mem_bot]
        exact hx
      · intro y1 y2 hy1 hy2 x hx
        obtain ⟨a, ha⟩ := hφ.surjective y1
        obtain ⟨b, hb⟩ := hφ.surjective y2
        have haM : a ∈ ⨆ i, (Xb i).comap φ := hy1 a ha
        have hbM : b ∈ ⨆ i, (Xb i).comap φ := hy2 b hb
        have hprod : a * b ∈ ⨆ i, (Xb i).comap φ := Subgroup.mul_mem _ haM hbM
        have hx' : x = (a * b) * ((a * b)⁻¹ * x) := by group
        rw [hx']
        refine Subgroup.mul_mem _ hprod ?_
        refine Subgroup.mem_iSup_of_mem i0 ?_
        rw [h0, Subgroup.mem_comap, Subgroup.mem_bot]
        rw [map_mul, map_inv, map_mul, ha, hb, hx]
        group
    intro x hx
    rw [Subgroup.mem_comap] at hx
    exact key (φ x) hx x rfl
  · refine iSup_le fun i => Subgroup.comap_mono (le_iSup Xb i)

private theorem wc813pbar_barPre_iSup {ι : Sort*} (hφ : IsBarMap H C φ) (Xb : ι → Subgroup Q)
    (i0 : ι) (h0 : Xb i0 = ⊥) :
    barPre H φ (⨆ i, Xb i) = ⨆ i, barPre H φ (Xb i) := by
  simp only [barPre]
  rw [wc813pbar_comap_iSup hφ Xb i0 h0, Subgroup.map_iSup]

theorem oTwoMod_barPre (hφ : IsBarMap H C φ) (hCH : C ≤ H) (Kb : Subgroup Q) :
    oTwoMod C (barPre H φ Kb) = barPre H φ (oTwoMod (⊥ : Subgroup Q) Kb) := by
  haveI : Finite Q := Finite.of_surjective φ hφ.surjective
  let s := wc813pbar_twoSet C (barPre H φ Kb)
  let sb := wc813pbar_twoSet (⊥ : Subgroup Q) Kb
  have hbot : (⊥ : Subgroup Q) ∈ sb := by
    refine ⟨le_rfl, bot_le, ?_, ?_⟩
    · rw [Subgroup.bot_subgroupOf]
      exact inferInstance
    · intro w hw
      exact ⟨0, by rw [Subgroup.mem_bot.mp hw]; simp⟩
  have hs : oTwoMod C (barPre H φ Kb) = ⨆ j : s, (j : Subgroup G) :=
    (wc813pbar_oTwoMod_eq C (barPre H φ Kb)).trans (iSup_subtype'' s id).symm
  have hreindex : (⨆ i : sb, barPre H φ (i : Subgroup Q)) = ⨆ j : s, (j : Subgroup G) := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      exact le_iSup (fun j : s => (j : Subgroup G))
        ⟨barPre H φ (i : Subgroup Q), wc813pbar_barPre_mem_twoSet hφ hCH i.2⟩
    · refine iSup_le fun j => ?_
      have hsub := wc813pbar_barSub_mem_twoSet hφ hCH j.2
      have heq : (j : Subgroup G) = barPre H φ (barSub H φ (j : Subgroup G)) :=
        (wc813pbar_barPre_barSub hφ j.2.1 (j.2.2.1.trans (barPre_le H φ Kb))).symm
      rw [heq]
      exact le_iSup (fun i : sb => barPre H φ (i : Subgroup Q))
        ⟨barSub H φ (j : Subgroup G), hsub⟩
  have hcomm : barPre H φ (⨆ i : sb, (i : Subgroup Q)) =
      ⨆ i : sb, barPre H φ (i : Subgroup Q) :=
    wc813pbar_barPre_iSup hφ (fun i : sb => (i : Subgroup Q)) ⟨⊥, hbot⟩ rfl
  calc oTwoMod C (barPre H φ Kb) = ⨆ j : s, (j : Subgroup G) := hs
    _ = ⨆ i : sb, barPre H φ (i : Subgroup Q) := hreindex.symm
    _ = barPre H φ (⨆ i : sb, (i : Subgroup Q)) := hcomm.symm
    _ = barPre H φ (oTwoMod (⊥ : Subgroup Q) Kb) := by
          congr 1
          exact (iSup_subtype'' sb id).trans (wc813pbar_oTwoMod_eq ⊥ Kb).symm

private def wc813pbar_oddSet (N P : Subgroup G) : Set (Subgroup G) :=
  {Q | N ≤ Q ∧ Q ≤ P ∧ (Q.subgroupOf P).Normal ∧ Odd (Q.relIndex P)}

private theorem wc813pbar_oddResMod_eq (N P : Subgroup G) :
    oddResMod N P = ⨅ Q ∈ wc813pbar_oddSet N P, Q := rfl

private theorem wc813pbar_barSub_mem_oddSet (hφ : IsBarMap H C φ) (hCH : C ≤ H)
    {Pb : Subgroup Q} {Y : Subgroup G} (hY : Y ∈ wc813pbar_oddSet C (barPre H φ Pb)) :
    barSub H φ Y ∈ wc813pbar_oddSet (⊥ : Subgroup Q) Pb := by
  obtain ⟨hCY, hYP, hYnorm, hYodd⟩ := hY
  have hbarYP : barSub H φ Y ≤ Pb := by
    have h' := wc813pbar_barSub_mono (φ := φ) (H := H) hYP
    rwa [barSub_barPre hφ Pb] at h'
  refine ⟨bot_le, hbarYP, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hbarYP]
    have hPnorm : barPre H φ Pb ≤ Subgroup.normalizer (Y : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYP).mp hYnorm
    have h' := barSub_le_normalizer_barSub φ (A := barPre H φ Pb) (B := Y) hPnorm
    rwa [barSub_barPre hφ Pb] at h'
  · rw [← wc813pbar_relIndex_barPre hφ hCH hCY hYP]
    exact hYodd

private theorem wc813pbar_barPre_mem_oddSet (hφ : IsBarMap H C φ) (hCH : C ≤ H)
    {Pb : Subgroup Q} {Yb : Subgroup Q} (hYb : Yb ∈ wc813pbar_oddSet (⊥ : Subgroup Q) Pb) :
    barPre H φ Yb ∈ wc813pbar_oddSet C (barPre H φ Pb) := by
  obtain ⟨-, hYbP, hYbnorm, hYbodd⟩ := hYb
  have hle : barPre H φ Yb ≤ barPre H φ Pb := wc813pbar_barPre_mono hYbP
  refine ⟨le_barPre hCH hφ Yb, hle, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    have hPnorm : Pb ≤ Subgroup.normalizer (Yb : Set Q) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYbP).mp hYbnorm
    have h' := le_normalizer_barPre hφ (A := barPre H φ Pb) (Xb := Yb)
      (barPre_le H φ Pb) (by rwa [barSub_barPre hφ Pb])
    exact h'
  · rw [wc813pbar_relIndex_barPre hφ hCH (le_barPre hCH hφ Yb) hle, barSub_barPre hφ Yb]
    exact hYbodd

private theorem wc813pbar_barPre_iInf {ι : Sort*} [Nonempty ι] (Xb : ι → Subgroup Q) :
    barPre H φ (⨅ i, Xb i) = ⨅ i, barPre H φ (Xb i) := by
  simp only [barPre]
  rw [Subgroup.comap_iInf, Subgroup.map_iInf H.subtype H.subtype_injective]

theorem oddResMod_barPre (hφ : IsBarMap H C φ) (hCH : C ≤ H) (Pb : Subgroup Q) :
    oddResMod C (barPre H φ Pb) = barPre H φ (oddResMod (⊥ : Subgroup Q) Pb) := by
  haveI : Finite Q := Finite.of_surjective φ hφ.surjective
  let s := wc813pbar_oddSet C (barPre H φ Pb)
  let sb := wc813pbar_oddSet (⊥ : Subgroup Q) Pb
  have hPb : Pb ∈ sb := by
    refine ⟨bot_le, le_rfl, ?_, ?_⟩
    · rw [Subgroup.subgroupOf_self]
      exact inferInstance
    · rw [Subgroup.relIndex_self]
      norm_num
  have hPbar : barPre H φ Pb ∈ s := by
    refine ⟨le_barPre hCH hφ Pb, le_rfl, ?_, ?_⟩
    · rw [Subgroup.subgroupOf_self]
      exact inferInstance
    · rw [Subgroup.relIndex_self]
      norm_num
  haveI : Nonempty sb := ⟨⟨Pb, hPb⟩⟩
  have hs : oddResMod C (barPre H φ Pb) = ⨅ j : s, (j : Subgroup G) :=
    (wc813pbar_oddResMod_eq C (barPre H φ Pb)).trans (iInf_subtype'' s id).symm
  have hreindex : (⨅ i : sb, barPre H φ (i : Subgroup Q)) = ⨅ j : s, (j : Subgroup G) := by
    apply le_antisymm
    · refine le_iInf fun j => ?_
      exact iInf_le_of_le
        ⟨barSub H φ (j : Subgroup G), wc813pbar_barSub_mem_oddSet hφ hCH j.2⟩
        (le_of_eq (wc813pbar_barPre_barSub hφ j.2.1 (j.2.2.1.trans (barPre_le H φ Pb))))
    · refine le_iInf fun i => ?_
      exact iInf_le_of_le
        ⟨barPre H φ (i : Subgroup Q), wc813pbar_barPre_mem_oddSet hφ hCH i.2⟩ le_rfl
  have hcomm : barPre H φ (⨅ i : sb, (i : Subgroup Q)) =
      ⨅ i : sb, barPre H φ (i : Subgroup Q) :=
    wc813pbar_barPre_iInf (φ := φ) (fun i : sb => (i : Subgroup Q))
  calc oddResMod C (barPre H φ Pb) = ⨅ j : s, (j : Subgroup G) := hs
    _ = ⨅ i : sb, barPre H φ (i : Subgroup Q) := hreindex.symm
    _ = barPre H φ (⨅ i : sb, (i : Subgroup Q)) := hcomm.symm
    _ = barPre H φ (oddResMod (⊥ : Subgroup Q) Pb) := by
          congr 1
          exact (iInf_subtype'' sb id).trans (wc813pbar_oddResMod_eq ⊥ Pb).symm

private theorem wc813pbar_barPre_lt (hφ : IsBarMap H C φ) {Xb Yb : Subgroup Q} :
    barPre H φ Xb < barPre H φ Yb ↔ Xb < Yb := by
  constructor
  · intro h
    have hle : Xb ≤ Yb := by
      have h' := wc813pbar_barSub_mono (φ := φ) (H := H) h.le
      rwa [barSub_barPre hφ Xb, barSub_barPre hφ Yb] at h'
    exact lt_of_le_of_ne hle fun heq => h.ne (by rw [heq])
  · intro h
    exact lt_of_le_of_ne (wc813pbar_barPre_mono h.le) fun heq => h.ne (by
      have h' := congrArg (barSub H φ) heq
      rwa [barSub_barPre hφ Xb, barSub_barPre hφ Yb] at h')

theorem isMaxParabolicMod_barPre (hφ : IsBarMap H C φ) (hCH : C ≤ H) {Lb Pb : Subgroup Q}
    (h : IsMaxParabolicMod (⊥ : Subgroup Q) Lb Pb) :
    IsMaxParabolicMod C (barPre H φ Lb) (barPre H φ Pb) := by
  obtain ⟨-, hPbLt, hmax, S, -, hSL, hSpow, hSodd, hSnorm⟩ := h
  refine ⟨le_barPre hCH hφ Pb, (wc813pbar_barPre_lt hφ).mpr hPbLt, ?_, ?_⟩
  · intro Y hYlt hYLE
    have hCY : C ≤ Y := (le_barPre hCH hφ Pb).trans hYlt.le
    have hYH : Y ≤ H := hYLE.trans (barPre_le H φ Lb)
    have hYb_le : barSub H φ Y ≤ Lb := by
      have h' := wc813pbar_barSub_mono (φ := φ) (H := H) hYLE
      rwa [barSub_barPre hφ Lb] at h'
    have hPb_lt_Yb : Pb < barSub H φ Y := by
      have hle : Pb ≤ barSub H φ Y := by
        have h' := wc813pbar_barSub_mono (φ := φ) (H := H) hYlt.le
        rwa [barSub_barPre hφ Pb] at h'
      refine lt_of_le_of_ne hle ?_
      intro heq
      apply hYlt.ne
      rw [← wc813pbar_barPre_barSub hφ hCY hYH, heq]
    have hEq := hmax (barSub H φ Y) hPb_lt_Yb hYb_le
    rw [← wc813pbar_barPre_barSub hφ hCY hYH, hEq]
  · refine ⟨barPre H φ S, le_barPre hCH hφ S, wc813pbar_barPre_mono hSL, ?_, ?_, ?_⟩
    · intro s hs
      obtain ⟨hsH, hsS⟩ := mem_barPre.mp hs
      obtain ⟨k, hk⟩ := hSpow (φ ⟨s, hsH⟩) hsS
      refine ⟨k, ?_⟩
      have hker : φ ((⟨s, hsH⟩ : ↥H) ^ 2 ^ k) = 1 := by
        rw [map_pow, Subgroup.mem_bot.mp hk]
      have h' := (hφ.ker_iff ((⟨s, hsH⟩ : ↥H) ^ 2 ^ k)).mp hker
      simpa using h'
    · rw [wc813pbar_relIndex_barPre hφ hCH (le_barPre hCH hφ S) (wc813pbar_barPre_mono hSL),
          barSub_barPre hφ S]
      exact hSodd
    · let Z := barPre H φ Lb ⊓
          Subgroup.normalizer ((barPre H φ S : Subgroup G) : Set G)
      have hCY : C ≤ Z := le_inf (le_barPre hCH hφ Lb)
        ((le_barPre hCH hφ S).trans (barPre H φ S).le_normalizer)
      have hYH : Z ≤ H := inf_le_left.trans (barPre_le H φ Lb)
      have hbarY : barSub H φ Z ≤ Pb := by
        have h1 : barSub H φ Z ≤ Lb := by
          have h' := wc813pbar_barSub_mono (φ := φ) (H := H)
            (inf_le_left : Z ≤ barPre H φ Lb)
          rwa [barSub_barPre hφ Lb] at h'
        have h2 : barSub H φ Z ≤ Subgroup.normalizer ((S : Subgroup Q) : Set Q) := by
          have h2a := wc813pbar_barSub_mono (φ := φ) (H := H)
            (inf_le_right : Z ≤ Subgroup.normalizer ((barPre H φ S : Subgroup G) : Set G))
          have h2b := wc813pbar_barSub_normalizer_le (φ := φ) (H := H)
            (S' := barPre H φ S) (barPre_le H φ S)
          have h' := h2a.trans h2b
          rwa [barSub_barPre hφ S] at h'
        exact (le_inf h1 h2).trans hSnorm
      change Z ≤ barPre H φ Pb
      rw [← wc813pbar_barPre_barSub hφ hCY hYH]
      exact wc813pbar_barPre_mono hbarY

end Bar

end CFSG.LocalAnalysis.WeakClosure81

end
