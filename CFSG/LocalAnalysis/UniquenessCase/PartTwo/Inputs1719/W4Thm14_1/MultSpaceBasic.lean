module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.MultSpaceHomog
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.MultSpaceSpanRank
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.TwoSummands
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.MultSpaceSpan

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem msb_rk_fixV_eq_four [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {T : Subgroup (MulAut W)} (h16 : Nat.card ↥(fixV T) = 16) :
    rk ↥(fixV T) = 4 := by
  have h := card_eq_two_pow hW (fixV T)
  rw [h16] at h
  have h' : 2 ^ rk ↥(fixV T) = 2 ^ 4 := by
    rw [← h]
    norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h'

private theorem msb_rk_eq_twelve [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L T : Subgroup (MulAut W)} (hfix : fixV L = ⊥)
    (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {J : Subgroup W}
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I)
    (hJ : J ∈ irrSet L) (h3 : ∀ I ∈ irrSet L, rk ↥I = 3) (hTL : T ≤ L)
    (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2)
    (h16 : Nat.card ↥(fixV T) = 16) : rk W = 12 := by
  have hU : rk ↥(fixV T) = 4 := msb_rk_fixV_eq_four hW h16
  have hJcard : rk ↥(J ⊓ fixV T) = 1 := by
    have h := card_eq_two_pow hW (J ⊓ fixV T)
    rw [hT J hJ] at h
    have h' : 2 ^ rk ↥(J ⊓ fixV T) = 2 ^ 1 := by
      rw [← h]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h'
  have hcount := rk_inf_fixV_mul_rk (W := W) hfix hspan (J := J)
    (CFSG.LocalAnalysis.WeakClosure81.stableUnder_of_mem_irrSet hJ) hhom hTL
    (X := T) (S := ⊤) (hS := fun _ _ _ _ => Subgroup.mem_top _)
  rw [top_inf_eq, rk_top, h3 J hJ, hJcard, one_mul, hU] at hcount
  omega

private theorem msb_rk_span_le [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L T : Subgroup (MulAut W)} (hfix : fixV L = ⊥)
    (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {J : Subgroup W}
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I)
    (hJ : J ∈ irrSet L) (h3 : ∀ I ∈ irrSet L, rk ↥I = 3) (hTL : T ≤ L)
    (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2) {A : Subgroup W}
    (hA : A ≤ fixV T) :
    rk ↥(⨆ g ∈ L, A.map (g : MulAut W).toMonoidHom) ≤ 3 * rk ↥A := by
  have h := rk_iSup_map_le (W := W) hW hfix hspan (J := J) hJ hhom hTL hT hA
  rwa [h3 J hJ] at h

private theorem msb_eq_top_of_span_eq_top [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L T : Subgroup (MulAut W)} (hfix : fixV L = ⊥)
    (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {J : Subgroup W}
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I)
    (hJ : J ∈ irrSet L) (h3 : ∀ I ∈ irrSet L, rk ↥I = 3) (hTL : T ≤ L)
    (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2)
    (h16 : Nat.card ↥(fixV T) = 16) {A' : Subgroup ↥(fixV T)}
    (htop : (⨆ g ∈ L, (A'.map (fixV T).subtype).map (g : MulAut W).toMonoidHom) = ⊤) :
    A' = ⊤ := by
  let U : Subgroup W := fixV T
  let A : Subgroup W := A'.map U.subtype
  have hA : A ≤ U := Subgroup.map_subtype_le A'
  have h12 : rk W = 12 := msb_rk_eq_twelve hW hfix hspan hhom hJ h3 hTL hT h16
  have h4 : rk U = 4 := msb_rk_fixV_eq_four hW h16
  have hle : rk ↥(⨆ g ∈ L, A.map (g : MulAut W).toMonoidHom) ≤ 3 * rk ↥A :=
    msb_rk_span_le hW hfix hspan hhom hJ h3 hTL hT hA
  have htopA : (⨆ g ∈ L, A.map (g : MulAut W).toMonoidHom) = ⊤ := htop
  have hrk : rk W = rk ↥(⨆ g ∈ L, A.map (g : MulAut W).toMonoidHom) := by
    rw [htopA, rk_top]
  have hAr : 4 ≤ rk ↥A := by omega
  have hAle : rk ↥A ≤ 4 := by
    have h := rk_mono hA
    rwa [h4] at h
  have hAr4 : rk ↥A = 4 := le_antisymm hAle hAr
  have hAU : A = U := eq_of_le_of_rk_le hW hA (by omega)
  have htopmap : (⊤ : Subgroup ↥U).map U.subtype = U := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  refine Subgroup.map_injective U.subtype_injective ?_
  show A'.map U.subtype = (⊤ : Subgroup ↥U).map U.subtype
  exact hAU.trans htopmap.symm

private theorem msb_exists_mem_irrSet [Finite W] {L : Subgroup (MulAut W)}
    (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {U : Subgroup W} (hU : Nat.card ↥U = 16) :
    ∃ J : Subgroup W, J ∈ irrSet L := by
  by_contra h
  push Not at h
  have hbot : (⨆ I ∈ irrSet L, I) = ⊥ := by
    rw [iSup_eq_bot]
    intro I
    rw [iSup_eq_bot]
    intro hI
    exact absurd hI (h I)
  have hcardW : Nat.card W = 1 := by
    have htopbot : (⊤ : Subgroup W) = ⊥ := by rw [← hspan, hbot]
    have hcard := congrArg (fun S : Subgroup W => Nat.card ↥S) htopbot
    simpa [Subgroup.card_top, Subgroup.card_bot] using hcard
  have hcardU : Nat.card ↥U ≤ Nat.card W := by
    simpa [Subgroup.card_top] using
      (Subgroup.card_le_of_le (H := U) (K := ⊤) le_top)
  omega

private theorem msb_stableUnder_map_of_stableUnder_autSub {M : Subgroup (MulAut W)}
    {U : Subgroup W} (hMU : M ≤ stabSub U) {A' : Subgroup ↥U}
    (hA' : StableUnder (autSub M U) A') : StableUnder M (A'.map U.subtype) := by
  intro m hm a ha
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  have hg : resHom U ⟨m, hMU hm⟩ ∈ autSub M U :=
    mem_autSub.mpr ⟨⟨m, hMU hm⟩, hm, rfl⟩
  exact Subgroup.mem_map.mpr
    ⟨resHom U ⟨m, hMU hm⟩ a', hA' _ hg a' ha', resHom_apply U _ a'⟩

private theorem msb_stableUnder_span_of_comm {L M : Subgroup (MulAut W)}
    (hMcent : M ≤ Subgroup.centralizer (L : Set (MulAut W)))
    {U : Subgroup W} (hMU : M ≤ stabSub U) {A' : Subgroup ↥U}
    (hA' : StableUnder (autSub M U) A') :
    StableUnder M (⨆ g ∈ L, (A'.map U.subtype).map (g : MulAut W).toMonoidHom) := by
  let A : Subgroup W := A'.map U.subtype
  have hA : StableUnder M A := msb_stableUnder_map_of_stableUnder_autSub hMU hA'
  intro m hm s hs
  rw [iSup_subtype'] at hs ⊢
  refine Subgroup.iSup_induction (fun g : ↥L => A.map (g : MulAut W).toMonoidHom)
    (C := fun y => m y ∈ ⨆ g : ↥L, A.map (g : MulAut W).toMonoidHom) hs ?_ ?_ ?_
  · intro g a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    have hcomm : Commute m (g : MulAut W) :=
      (commute_iff_eq m (g : MulAut W)).mpr
        (Subgroup.mem_centralizer_iff.mp (hMcent hm) (g : MulAut W) g.2).symm
    have hmul : m ((g : MulAut W) a₀) = (g : MulAut W) (m a₀) := by
      change (m * (g : MulAut W)) a₀ = ((g : MulAut W) * m) a₀
      rw [hcomm.eq]
    change m ((g : MulAut W) a₀) ∈ ⨆ g : ↥L, A.map (g : MulAut W).toMonoidHom
    rw [hmul]
    exact Subgroup.mem_iSup_of_mem g (Subgroup.mem_map_of_mem _ (hA m hm a₀ ha₀))
  · simp
  · intro x y hx hy
    rw [map_mul]
    exact Subgroup.mul_mem _ hx hy

private theorem msb_stableUnder_span {Y L M : Subgroup (MulAut W)}
    (hM : M = centGroupIn Y L) (hY : Y = L ⊔ M)
    {U : Subgroup W} (hMU : M ≤ stabSub U) {A' : Subgroup ↥U}
    (hA' : StableUnder (autSub M U) A') :
    StableUnder Y (⨆ g ∈ L, (A'.map U.subtype).map (g : MulAut W).toMonoidHom) := by
  let A : Subgroup W := A'.map U.subtype
  let S : Subgroup W := ⨆ g ∈ L, A.map (g : MulAut W).toMonoidHom
  have hMcent : M ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [hM]
    exact inf_le_right
  have hL : StableUnder L S := stableUnder_iSup_map (L := L) A
  have hMS : StableUnder M S := msb_stableUnder_span_of_comm hMcent hMU hA'
  intro y hy s hs
  obtain ⟨l, hl, m, hm, rfl⟩ := exists_mul_of_mem hM hY hy
  simpa only [MulAut.mul_apply] using hL l hl (m s) (hMS m hm s hs)

private theorem msb_sup_span (L : Subgroup (MulAut W)) (A₁ A₂ : Subgroup W) :
    (⨆ g ∈ L, A₁.map (g : MulAut W).toMonoidHom) ⊔
      (⨆ g ∈ L, A₂.map (g : MulAut W).toMonoidHom) =
    ⨆ g ∈ L, (A₁ ⊔ A₂).map (g : MulAut W).toMonoidHom := by
  refine le_antisymm (sup_le ?_ ?_) ?_
  · refine iSup₂_le fun g hg => ?_
    exact le_iSup₂_of_le g hg (Subgroup.map_mono le_sup_left)
  · refine iSup₂_le fun g hg => ?_
    exact le_iSup₂_of_le g hg (Subgroup.map_mono le_sup_right)
  · refine iSup₂_le fun g hg => ?_
    rw [Subgroup.map_sup]
    exact sup_le (le_trans (le_iSup₂_of_le g hg le_rfl) le_sup_left)
      (le_trans (le_iSup₂_of_le g hg le_rfl) le_sup_right)

private theorem msb_ne_bot_of_faithful {Y L M : Subgroup (MulAut W)}
    (hM : M = centGroupIn Y L) (hfix : fixV L = ⊥)
    (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {T : Subgroup (MulAut W)} (hTL : T ≤ L)
    (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2) (hM1 : M ≠ ⊥)
    {A' : Subgroup ↥(fixV T)}
    (hfaith : ∀ y ∈ autSub M (fixV T), (∀ u ∈ A', y u = u) → y = 1) :
    A' ≠ ⊥ := by
  intro hbot
  apply hM1
  rw [eq_bot_iff]
  intro m hm
  rw [Subgroup.mem_bot]
  have hMcent : M ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [hM]
    exact inf_le_right
  have hMU : M ≤ stabSub (fixV T) :=
    le_stabSub_fixV (hMcent.trans (Subgroup.centralizer_le hTL))
  let g : stabSub (fixV T) := ⟨m, hMU hm⟩
  have hresfix : ∀ u ∈ A', resHom (fixV T) g u = u := by
    intro u hu
    rw [hbot] at hu
    rw [Subgroup.mem_bot.mp hu]
    exact map_one (resHom (fixV T) g)
  have hres1 : resHom (fixV T) g = 1 :=
    hfaith _ (mem_autSub.mpr ⟨g, hm, rfl⟩) hresfix
  have hmU : ∀ u ∈ fixV T, m u = u := by
    intro u hu
    have h := congrArg (fun φ : MulAut ↥(fixV T) => ((φ ⟨u, hu⟩ : ↥(fixV T)) : W)) hres1
    simpa [resHom_apply] using h
  exact eq_one_of_mem_centralizer_of_forall_fixV hfix hspan hT (hMcent hm) hmU

private theorem msb_normal_fixer_eq_bot {L : Subgroup (MulAut W)}
    (hL3 : IsL3 ↥L 1) {S : Subgroup W} (hS_L : StableUnder L S)
    (hSnt : ¬ S ≤ fixV L) :
    (L ⊓ centSub S).subgroupOf L = ⊥ := by
  classical
  have hLstabS : L ≤ stabSub S :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.le_stabSub_of_stableUnder hS_L
  let K : Subgroup ↥L := (L ⊓ centSub S).subgroupOf L
  have hN : K.Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 ha.1) (L.inv_mem g.2), fun u hu => ?_⟩
    have hu' : (g : MulAut W)⁻¹ u ∈ S := (hLstabS (L.inv_mem g.2) u).2 hu
    change (g : MulAut W) ((a : MulAut W) ((g : MulAut W)⁻¹ u)) = u
    rw [ha.2 _ hu']
    simp
  have hKne : K ≠ ⊤ := by
    intro hK
    apply hSnt
    intro s hs
    rw [mem_fixV]
    intro l' hl'
    have hmem : (⟨l', hl'⟩ : ↥L) ∈ K := by rw [hK]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hmem).2 s hs
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥L _
    (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3) K hN with h | h
  · exact h
  · exact absurd h hKne

private theorem msb_commute_of_fix_span {L M : Subgroup (MulAut W)}
    (hMcent : M ≤ Subgroup.centralizer (L : Set (MulAut W)))
    {S : Subgroup W} (hLstabS : L ≤ stabSub S)
    (hKbot : (L ⊓ centSub S).subgroupOf L = ⊥)
    {l m : MulAut W} (hl : l ∈ L) (hm : m ∈ M)
    (hfixy : ∀ s ∈ S, (l * m) s = s) {l' : MulAut W} (hl' : l' ∈ L) :
    l' * l = l * l' := by
  classical
  have hcomm_lm : l * m = m * l :=
    Subgroup.mem_centralizer_iff.mp (hMcent hm) l hl
  have hcomm_l' : m * l'⁻¹ = l'⁻¹ * m := by
    have hc : Commute m l' :=
      (commute_iff_eq m l').mpr
        (Subgroup.mem_centralizer_iff.mp (hMcent hm) l' hl').symm
    exact hc.inv_right.eq
  have hcomm_l : m * l⁻¹ = l⁻¹ * m := by
    have hc : Commute m l :=
      (commute_iff_eq m l).mpr hcomm_lm.symm
    exact hc.inv_right.eq
  let w : MulAut W := l' * (l * m) * l'⁻¹ * (l * m)⁻¹
  have hyinv : (l * m)⁻¹ = l⁻¹ * m⁻¹ := by
    rw [hcomm_lm, mul_inv_rev]
  have hw_eq : w = l' * l * l'⁻¹ * l⁻¹ := by
    calc w = l' * (l * m) * l'⁻¹ * (l * m)⁻¹ := rfl
      _ = l' * (l * m) * l'⁻¹ * (l⁻¹ * m⁻¹) := by rw [hyinv]
      _ = l' * l * (m * l'⁻¹) * (l⁻¹ * m⁻¹) := by group
      _ = l' * l * (l'⁻¹ * m) * (l⁻¹ * m⁻¹) := by rw [hcomm_l']
      _ = l' * l * l'⁻¹ * (m * l⁻¹ * m⁻¹) := by group
      _ = l' * l * l'⁻¹ * l⁻¹ := by rw [hcomm_l]; group
  have hwL : w ∈ L := by
    rw [hw_eq]
    exact L.mul_mem (L.mul_mem (L.mul_mem hl' hl) (L.inv_mem hl')) (L.inv_mem hl)
  have hwfix : ∀ s ∈ S, w s = s := by
    intro s hs
    have hyfix : (l * m) s = s := hfixy s hs
    have hyinvfix : (l * m)⁻¹ s = s := by
      apply (l * m).injective
      rw [MulAut.apply_inv_self, hyfix]
    have hconjfix : (l' * (l * m) * l'⁻¹) s = s := by
      have hs1 : (l'⁻¹ : MulAut W) s ∈ S := (hLstabS (L.inv_mem hl') s).2 hs
      have hsplit : (l' * (l * m) * l'⁻¹) s = l' ((l * m) ((l'⁻¹) s)) := rfl
      rw [hsplit, hfixy _ hs1, MulAut.apply_inv_self]
    calc w s = (l' * (l * m) * l'⁻¹) ((l * m)⁻¹ s) := rfl
      _ = (l' * (l * m) * l'⁻¹) s := by rw [hyinvfix]
      _ = s := hconjfix
  have hwK : (⟨w, hwL⟩ : ↥L) ∈ (L ⊓ centSub S).subgroupOf L :=
    Subgroup.mem_subgroupOf.mpr ⟨hwL, mem_centSub.mpr hwfix⟩
  have hw1 : w = 1 := by
    have hzero : (⟨w, hwL⟩ : ↥L) ∈ (⊥ : Subgroup ↥L) := by
      rw [← hKbot]
      exact hwK
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hzero)
  have hbase : l' * l * l'⁻¹ * l⁻¹ = 1 := hw_eq.symm.trans hw1
  have h1 : l' * l * l'⁻¹ = l := by
    have h := congrArg (fun x => x * l) hbase
    simpa [mul_assoc] using h
  have h2 : l' * l = l * l' := by
    have h := congrArg (fun x => x * l') h1
    simpa [mul_assoc] using h
  exact h2

private theorem msb_eq_one_left_of_fix_span {L M : Subgroup (MulAut W)}
    (hL3 : IsL3 ↥L 1)
    (hMcent : M ≤ Subgroup.centralizer (L : Set (MulAut W)))
    {S : Subgroup W} (hS_L : StableUnder L S) (hSnt : ¬ S ≤ fixV L)
    {l m : MulAut W} (hl : l ∈ L) (hm : m ∈ M)
    (hfixy : ∀ s ∈ S, (l * m) s = s) : l = 1 := by
  have hLstabS : L ≤ stabSub S :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.le_stabSub_of_stableUnder hS_L
  have hKbot : (L ⊓ centSub S).subgroupOf L = ⊥ := msb_normal_fixer_eq_bot hL3 hS_L hSnt
  have hcomm_all : ∀ l' ∈ L, l' * l = l * l' := fun l' hl' =>
    msb_commute_of_fix_span hMcent hLstabS hKbot hl hm hfixy hl'
  have hlcent : l ∈ Subgroup.centralizer (L : Set (MulAut W)) :=
    Subgroup.mem_centralizer_iff.mpr hcomm_all
  have hlinf : l ∈ L ⊓ centGroupIn L L := ⟨hl, ⟨hl, hlcent⟩⟩
  have hlb : l ∈ (⊥ : Subgroup (MulAut W)) := by
    rw [← inf_centGroupIn_eq_bot (Y := L) hL3]
    exact hlinf
  exact Subgroup.mem_bot.mp hlb

private theorem msb_eq_one_of_fix_span {Y L M : Subgroup (MulAut W)}
    (hM : M = centGroupIn Y L) (hfix : fixV L = ⊥)
    (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {T : Subgroup (MulAut W)} (hTL : T ≤ L)
    (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2)
    {A' : Subgroup ↥(fixV T)}
    (hfaith : ∀ y ∈ autSub M (fixV T), (∀ u ∈ A', y u = u) → y = 1)
    {S : Subgroup W} (hAS : A'.map (fixV T).subtype ≤ S)
    {m : MulAut W} (hm : m ∈ M) (hmfix : ∀ s ∈ S, m s = s) : m = 1 := by
  have hMcent : M ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [hM]
    exact inf_le_right
  have hMU : M ≤ stabSub (fixV T) :=
    le_stabSub_fixV (hMcent.trans (Subgroup.centralizer_le hTL))
  let g : stabSub (fixV T) := ⟨m, hMU hm⟩
  have hresfix : ∀ u ∈ A', resHom (fixV T) g u = u := by
    intro u hu
    apply Subtype.ext
    rw [resHom_apply]
    exact hmfix _ (hAS (Subgroup.mem_map_of_mem (fixV T).subtype hu))
  have hres1 : resHom (fixV T) g = 1 :=
    hfaith _ (mem_autSub.mpr ⟨g, hm, rfl⟩) hresfix
  have hmU : ∀ u ∈ fixV T, m u = u := by
    intro u hu
    have h := congrArg (fun φ : MulAut ↥(fixV T) => ((φ ⟨u, hu⟩ : ↥(fixV T)) : W)) hres1
    simpa [resHom_apply] using h
  exact eq_one_of_mem_centralizer_of_forall_fixV hfix hspan hT (hMcent hm) hmU

private theorem msb_eq_top_of_faithful [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L M : Subgroup (MulAut W)} (hL3 : IsL3 ↥L 1) (hM : M = centGroupIn Y L)
    (hY : Y = L ⊔ M) (hfix : fixV L = ⊥) (htr : IrrSpanTrans Y L)
    (hbasic : IsBasicModule Y) {T : Subgroup (MulAut W)} (hTL : T ≤ L)
    (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2)
    (h3 : ∀ I ∈ irrSet L, rk ↥I = 3) (h16 : Nat.card ↥(fixV T) = 16) (hM1 : M ≠ ⊥)
    {J : Subgroup W} (hJ : J ∈ irrSet L)
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I)
    {A' : Subgroup ↥(fixV T)} (hAinv : StableUnder (autSub M (fixV T)) A')
    (hfaith : ∀ y ∈ autSub M (fixV T), (∀ u ∈ A', y u = u) → y = 1) :
    A' = ⊤ := by
  let U : Subgroup W := fixV T
  let A : Subgroup W := A'.map U.subtype
  let S : Subgroup W := ⨆ g ∈ L, A.map (g : MulAut W).toMonoidHom
  have hspan : (⨆ I ∈ irrSet L, I) = ⊤ := htr.1
  have hMcent : M ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [hM]
    exact inf_le_right
  have hMU : M ≤ stabSub U :=
    le_stabSub_fixV (hMcent.trans (Subgroup.centralizer_le hTL))
  have hA'ne : A' ≠ ⊥ :=
    msb_ne_bot_of_faithful hM hfix hspan hTL hT hM1 hfaith
  have hAne : A ≠ ⊥ := fun h =>
    hA'ne ((Subgroup.map_eq_bot_iff_of_injective (H := A') (f := U.subtype)
      U.subtype_injective).mp h)
  have hA_le_S : A ≤ S := by
    intro a ha
    exact Subgroup.mem_iSup_of_mem (1 : MulAut W)
      (Subgroup.mem_iSup_of_mem L.one_mem (by simpa using ha))
  have hSnt : ¬ S ≤ fixV L := by
    intro hSle
    have hAle : A ≤ fixV L := hA_le_S.trans hSle
    rw [hfix] at hAle
    exact hAne (le_antisymm hAle bot_le)
  have hS_L : StableUnder L S := stableUnder_iSup_map (L := L) A
  have hS_Y : StableUnder Y S := msb_stableUnder_span hM hY hMU hAinv
  have hYfaith : ∀ y ∈ Y, (∀ s ∈ S, y s = s) → y = 1 := by
    intro y hy hyfix
    obtain ⟨l, hl, m, hm, rfl⟩ := exists_mul_of_mem hM hY hy
    have hl1 : l = 1 := msb_eq_one_left_of_fix_span hL3 hMcent hS_L hSnt hl hm hyfix
    rw [hl1, one_mul] at hyfix ⊢
    exact msb_eq_one_of_fix_span hM hfix hspan hTL hT hfaith hA_le_S hm hyfix
  have hStop : S = ⊤ := hbasic.2 S hS_Y hYfaith
  exact msb_eq_top_of_span_eq_top hW hfix hspan hhom hJ h3 hTL hT h16
    (by simpa [S, A, U] using hStop)

theorem isBasicModule_autSub [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y L M : Subgroup (MulAut W)}
    (hL3 : IsL3 ↥L 1) (hM : M = centGroupIn Y L) (hY : Y = L ⊔ M) (hfix : fixV L = ⊥)
    (htr : IrrSpanTrans Y L) (hbasic : IsBasicModule Y) {T : Subgroup (MulAut W)} (hTL : T ≤ L)
    (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2) (h3 : ∀ I ∈ irrSet L, rk ↥I = 3)
    (h16 : Nat.card ↥(fixV T) = 16) (hM1 : M ≠ ⊥) : IsBasicModule (autSub M (fixV T)) := by
  classical
  have hspan : (⨆ I ∈ irrSet L, I) = ⊤ := htr.1
  have hMcent : M ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [hM]
    exact inf_le_right
  have hMU : M ≤ stabSub (fixV T) :=
    le_stabSub_fixV (hMcent.trans (Subgroup.centralizer_le hTL))
  obtain ⟨J, hJ⟩ := msb_exists_mem_irrSet (L := L) (U := fixV T) hspan h16
  have hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I := fun I hI =>
    isoMod_of_mem_irrSet (I := J) (J := I) hM hY hfix htr hJ hI
  constructor
  · intro A₁' A₂' hA₁ hA₂ htop12
    let A₁ : Subgroup W := A₁'.map (fixV T).subtype
    let A₂ : Subgroup W := A₂'.map (fixV T).subtype
    have hS₁ : StableUnder Y (⨆ g ∈ L, A₁.map (g : MulAut W).toMonoidHom) :=
      msb_stableUnder_span hM hY hMU hA₁
    have hS₂ : StableUnder Y (⨆ g ∈ L, A₂.map (g : MulAut W).toMonoidHom) :=
      msb_stableUnder_span hM hY hMU hA₂
    have hAunion : A₁ ⊔ A₂ = fixV T := by
      have hmap : (A₁' ⊔ A₂').map (fixV T).subtype = fixV T := by
        rw [htop12]
        rw [Subgroup.map_top, Subgroup.range_subtype]
      rwa [Subgroup.map_sup] at hmap
    have hStop : (⨆ g ∈ L, A₁.map (g : MulAut W).toMonoidHom) ⊔
        (⨆ g ∈ L, A₂.map (g : MulAut W).toMonoidHom) = ⊤ := by
      rw [msb_sup_span, hAunion]
      exact iSup_map_fixV_eq_top hfix hspan hT
    rcases hbasic.1 _ _ hS₁ hS₂ hStop with h | h
    · exact Or.inl (msb_eq_top_of_span_eq_top hW hfix hspan hhom hJ h3 hTL hT h16
        (by simpa [A₁] using h))
    · exact Or.inr (msb_eq_top_of_span_eq_top hW hfix hspan hhom hJ h3 hTL hT h16
        (by simpa [A₂] using h))
  · intro A' hAinv hfaith
    exact msb_eq_top_of_faithful hW hL3 hM hY hfix htr hbasic hTL hT h3 h16 hM1 hJ hhom
      hAinv hfaith

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace
