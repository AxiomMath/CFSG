module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Rad
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Fin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}
  {G' : Type} [Group G']

theorem w183b2_imgOf_iSup {ψ : ↥Y →* G'} {ι : Sort*} (A : ι → Subgroup (LGL 2 V))
    (hA : ∀ i, A i ≤ Y) : imgOf ψ (⨆ i, A i) = ⨆ i, imgOf ψ (A i) := by
  have hsub : (⨆ i, A i).subgroupOf Y = ⨆ i, (A i).subgroupOf Y := by
    refine le_antisymm ?_ (iSup_comap_le Y.subtype A)
    intro x hx
    have hx' : (x : LGL 2 V) ∈ (⨆ i, (A i).subgroupOf Y).map Y.subtype := by
      rw [Subgroup.map_iSup]
      exact (iSup_congr fun i => Subgroup.map_subgroupOf_eq_of_le (hA i)).symm ▸ hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    exact (Subtype.ext hyx) ▸ hy
  show ((⨆ i, A i).subgroupOf Y).map ψ = ⨆ i, imgOf ψ (A i)
  rw [hsub, Subgroup.map_iSup]
  rfl

private theorem w183b2_imgOf_eq_iff {ψ : ↥Y →* G'} (hψ : Function.Injective ψ)
    {A B : Subgroup (LGL 2 V)} (hA : A ≤ Y) (hB : B ≤ Y) :
    imgOf ψ A = imgOf ψ B ↔ A = B := by
  constructor
  · intro h
    exact le_antisymm ((imgOf_le_iff hψ hA hB).mp h.le) ((imgOf_le_iff hψ hB hA).mp h.ge)
  · intro h; rw [h]

private theorem w183b2_cj_le {p : LGL 2 V} (hp : p ∈ Y) {X : Subgroup (LGL 2 V)}
    (hX : X ≤ Y) : cj p X ≤ Y := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  have haY : a ∈ Y := hX ha
  show (MulAut.conj p) a ∈ Y
  rw [MulAut.conj_apply]
  exact Y.mul_mem (Y.mul_mem hp haY) (Y.inv_mem hp)

private theorem w183b2_mem_normalizer_imgOf_iff {ψ : ↥Y →* G'} (hψ : Function.Injective ψ)
    {B : Subgroup (LGL 2 V)} (hB : B ≤ Y) {p : LGL 2 V} (hp : p ∈ Y) :
    ψ ⟨p, hp⟩ ∈ Subgroup.normalizer (imgOf ψ B : Set G') ↔
      p ∈ Subgroup.normalizer (B : Set (LGL 2 V)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.mem_normalizer_iff_map_conj_eq]
  change (imgOf ψ B).map (MulAut.conj (ψ ⟨p, hp⟩)).toMonoidHom = imgOf ψ B ↔
    B.map (MulAut.conj p).toMonoidHom = B
  rw [show (imgOf ψ B).map (MulAut.conj (ψ ⟨p, hp⟩)).toMonoidHom = imgOf ψ (cj p B) from
    (imgOf_cj ψ hB hp).symm]
  change imgOf ψ (cj p B) = imgOf ψ B ↔ cj p B = B
  rw [w183b2_imgOf_eq_iff hψ (w183b2_cj_le hp hB) hB]

private theorem w183b2_isElemAbelian_of_le {E B : Subgroup (LGL 2 V)} (hE : IsElemAbelian 2 E)
    (hBE : B ≤ E) : IsElemAbelian 2 B := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · exact Subtype.ext (congrArg (Subtype.val : ↥E → LGL 2 V)
      (hE.1.is_comm.comm (⟨(x : LGL 2 V), hBE x.2⟩ : ↥E)
        (⟨(y : LGL 2 V), hBE y.2⟩ : ↥E)))
  · change (x : LGL 2 V) ^ 2 = 1
    exact hE.2 (x : LGL 2 V) (hBE hx)

private theorem w183b2_mul_self_eq_one {E : Subgroup (LGL 2 V)} (hE : IsElemAbelian 2 E)
    {x : LGL 2 V} (hx : x ∈ E) : x * x = 1 := by
  simpa [pow_two] using hE.2 x hx

private theorem w183b2_le_normalizer_inf (hTY : T ≤ Y) (hLY : L ≤ Y)
    (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L) :
    T ≤ Subgroup.normalizer (T ⊓ L : Set (LGL 2 V)) := by
  refine (Subgroup.le_normalizer_iff (G := LGL 2 V) (H := T) (K := T ⊓ L)).mpr ?_
  intro t ht k hk
  exact ⟨T.mul_mem (T.mul_mem ht hk.1) (T.inv_mem ht), hLn t (hTY ht) k hk.2⟩

private theorem w183b2_imgOf_le_invGen {ψ : ↥Y →* MulAut ↥L} {B : Subgroup (LGL 2 V)}
    (hBY : B ≤ Y) (hBT : B ≤ T) (hBe : IsElemAbelian 2 B) :
    imgOf ψ B ≤ invGen (imgOf ψ T) := by
  intro x hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · exact apply_mem_imgOf ψ (hBT hb) b.2
  · have hbb : (b : LGL 2 V) * (b : LGL 2 V) = 1 := w183b2_mul_self_eq_one hBe hb
    have hbY : (b : ↥Y) * b = 1 := Subtype.ext hbb
    calc ψ b * ψ b = ψ (b * b) := (map_mul ψ b b).symm
      _ = ψ 1 := by rw [hbY]
      _ = 1 := map_one ψ

private theorem w183b2_imgOf_gen_sup (hL : SimpleCore Y L) {X Q : Subgroup (LGL 2 V)}
    (hX : X ≤ Y) (hQ : Q ≤ Y) :
    imgOf (psiOf Y L hL.normal)
        (⨆ p ∈ L ⊓ Subgroup.normalizer (Q : Set (LGL 2 V)), cj p X) =
      ⨆ q ∈ innAutOf ↥L ⊓ Subgroup.normalizer
          (imgOf (psiOf Y L hL.normal) Q : Set (MulAut ↥L)),
        autConj q (imgOf (psiOf Y L hL.normal) X) := by
  set ψ := psiOf Y L hL.normal with hψdef
  have hψ : Function.Injective ψ := psiOf_injective hL
  have houter : ∀ p : LGL 2 V,
      (⨆ (_ : p ∈ L ⊓ Subgroup.normalizer (Q : Set (LGL 2 V))), cj p X) ≤ Y :=
    fun p => iSup_le fun hp => w183b2_cj_le (hL.le hp.1) hX
  have hinner : ∀ p : LGL 2 V, imgOf ψ
      (⨆ (_ : p ∈ L ⊓ Subgroup.normalizer (Q : Set (LGL 2 V))), cj p X) =
      ⨆ (_ : p ∈ L ⊓ Subgroup.normalizer (Q : Set (LGL 2 V))), imgOf ψ (cj p X) :=
    fun p => w183b2_imgOf_iSup
      (fun _ : p ∈ L ⊓ Subgroup.normalizer (Q : Set (LGL 2 V)) => cj p X)
      (fun hp => w183b2_cj_le (hL.le hp.1) hX)
  have step1 : imgOf ψ (⨆ p ∈ L ⊓ Subgroup.normalizer (Q : Set (LGL 2 V)), cj p X) =
      ⨆ p : LGL 2 V, imgOf ψ
        (⨆ (_ : p ∈ L ⊓ Subgroup.normalizer (Q : Set (LGL 2 V))), cj p X) :=
    w183b2_imgOf_iSup (fun p =>
      ⨆ (_ : p ∈ L ⊓ Subgroup.normalizer (Q : Set (LGL 2 V))), cj p X) houter
  have step2 : (⨆ p : LGL 2 V, imgOf ψ
        (⨆ (_ : p ∈ L ⊓ Subgroup.normalizer (Q : Set (LGL 2 V))), cj p X)) =
      ⨆ p ∈ L ⊓ Subgroup.normalizer (Q : Set (LGL 2 V)), imgOf ψ (cj p X) :=
    iSup_congr fun p => hinner p
  have hLHS : imgOf ψ (⨆ p ∈ L ⊓ Subgroup.normalizer (Q : Set (LGL 2 V)), cj p X) =
      ⨆ p ∈ L ⊓ Subgroup.normalizer (Q : Set (LGL 2 V)), imgOf ψ (cj p X) :=
    step1.trans step2
  rw [hLHS]
  apply le_antisymm
  · refine iSup_le fun p => iSup_le fun hp => ?_
    rw [imgOf_cj ψ hX (hL.le hp.1)]
    refine le_iSup_of_le (ψ ⟨p, hL.le hp.1⟩) (le_iSup_of_le ?_ le_rfl)
    refine ⟨?_, ?_⟩
    · rw [← imgOf_psiOf_L hL]
      exact apply_mem_imgOf ψ hp.1 (hL.le hp.1)
    · exact (w183b2_mem_normalizer_imgOf_iff hψ hQ (hL.le hp.1)).mpr hp.2
  · refine iSup_le fun q => iSup_le fun hq => ?_
    obtain ⟨l, hl, hlq⟩ := exists_psiOf_eq_of_mem_innAutOf hL hq.1
    have hlN : l ∈ Subgroup.normalizer (Q : Set (LGL 2 V)) := by
      apply (w183b2_mem_normalizer_imgOf_iff hψ hQ (hL.le hl)).mp
      rw [hlq]
      exact hq.2
    refine le_iSup_of_le l (le_iSup_of_le (show l ∈ L ⊓ Subgroup.normalizer
      (Q : Set (LGL 2 V)) from ⟨hl, hlN⟩) ?_)
    rw [← hlq, imgOf_cj ψ hX (hL.le hl)]
    rfl

theorem w183b2_sp44_no_r2 (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ) (hL : Br2OneComp Y T L)
    (hrange : (psiOf Y L hL.normal).range = ⊤) {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ)
    {g : MulAut ↥L}
    (hgP : autConj g (imgOf (psiOf Y L hL.normal) D) ≤ imgOf (psiOf Y L hL.normal) T)
    (hinv : invGen (imgOf (psiOf Y L hL.normal) T) ≤
      Subgroup.normalizer (autConj g (imgOf (psiOf Y L hL.normal) D) : Set (MulAut ↥L)))
    (hN : ¬ Subgroup.normalizer
      ((imgOf (psiOf Y L hL.normal) T ⊓ innAutOf ↥L : Subgroup (MulAut ↥L)) : Set (MulAut ↥L)) ≤
      Subgroup.normalizer (autConj g (imgOf (psiOf Y L hL.normal) D) : Set (MulAut ↥L))) :
    False := by
  set ψ := psiOf Y L hL.normal with hψdef
  have hψ : Function.Injective ψ := psiOf_injective hL.core
  have hTY : T ≤ Y := hc.sylow.le
  have hLY : L ≤ Y := hL.le
  have hSLY : T ⊓ L ≤ Y := fun x hx => hTY hx.1
  obtain ⟨y, hyg⟩ : ∃ y : ↥Y, ψ y = g := by
    have : g ∈ ψ.range := by rw [hrange]; exact Subgroup.mem_top g
    exact MonoidHom.mem_range.mp this
  rw [← hyg] at hgP hinv hN
  have hD' : cj (y : LGL 2 V) D ∈ Γ := hc.h131.invariant D hD (y : LGL 2 V) y.2
  have hD'Y : cj (y : LGL 2 V) D ≤ Y := hc.h131.le_G _ hD'
  have hD'T : cj (y : LGL 2 V) D ≤ T := by
    rw [← imgOf_le_iff hψ hD'Y hTY, imgOf_cj ψ (hc.h131.le_G D hD) y.2]
    exact hgP
  have hX : Y ⊓ Subgroup.normalizer (T ⊓ L : Set (LGL 2 V)) ≤ Y := inf_le_left
  have hTX : T ≤ Y ⊓ Subgroup.normalizer (T ⊓ L : Set (LGL 2 V)) :=
    fun t ht => ⟨hTY ht, w183b2_le_normalizer_inf hTY hLY hL.normal ht⟩
  have hXne : Y ⊓ Subgroup.normalizer (T ⊓ L : Set (LGL 2 V)) ≠ Y := by
    intro h
    exact w183b2_normalizer_sylow_ne hL hc.sylow (h.ge.trans inf_le_right)
  have hB : ∀ B ∈ 𝒢, B ≤ Subgroup.normalizer (cj (y : LGL 2 V) D : Set (LGL 2 V)) := by
    intro B hB
    obtain ⟨hBT, D'', hD'', hBD'', _⟩ := hc.gens B hB
    have hBY : B ≤ Y := fun b hb => hTY (hBT hb)
    have hBe : IsElemAbelian 2 B :=
      w183b2_isElemAbelian_of_le (hc.h131.isElemAb D'' hD'') hBD''
    rw [← imgOf_normalizer_le_iff hψ hBY hD'Y, imgOf_cj ψ (hc.h131.le_G D hD) y.2]
    exact (w183b2_imgOf_le_invGen hBY hBT hBe).trans hinv
  have hw := hc.weakClosure (cj (y : LGL 2 V) D) hD' hD'T hB
    (Y ⊓ Subgroup.normalizer (T ⊓ L : Set (LGL 2 V))) hX hTX hXne
  apply hN
  intro a ha
  have hamem : a ∈ ψ.range := by rw [hrange]; exact Subgroup.mem_top a
  obtain ⟨y₁, hy₁a⟩ := MonoidHom.mem_range.mp hamem
  have hS' : imgOf ψ (T ⊓ L) = imgOf ψ T ⊓ innAutOf ↥L := by
    rw [(imgOf_sup_inf hψ hTY hLY).2, imgOf_psiOf_L hL.core]
  have hmemN : a ∈ Subgroup.normalizer (imgOf ψ (T ⊓ L) : Set (MulAut ↥L)) := by
    rwa [hS']
  rw [← hy₁a] at hmemN
  have hy₁N : (y₁ : LGL 2 V) ∈ Subgroup.normalizer (T ⊓ L : Set (LGL 2 V)) :=
    (w183b2_mem_normalizer_imgOf_iff hψ hSLY y₁.2).mp hmemN
  have hy₁ND : (y₁ : LGL 2 V) ∈
      Subgroup.normalizer (cj (y : LGL 2 V) D : Set (LGL 2 V)) :=
    hw ⟨y₁.2, hy₁N⟩
  rw [← hy₁a]
  rw [show autConj (ψ y) (imgOf ψ D) = imgOf ψ (cj (y : LGL 2 V) D) from
    (imgOf_cj ψ (hc.h131.le_G D hD) y.2).symm]
  exact (w183b2_mem_normalizer_imgOf_iff hψ hD'Y y₁.2).mpr hy₁ND

theorem br2RadY_of_two_radicals (hT : IsSylowIn 2 T Y) (hL : Br2OneComp Y T L)
    {Q₁' Q₂' : Subgroup (MulAut ↥L)}
    (hrad : Br2TwoRadicals ↥L (imgOf (psiOf Y L hL.normal) T ⊓ innAutOf ↥L) Q₁' Q₂') :
    ∃ Q₁ Q₂ : Subgroup (LGL 2 V), imgOf (psiOf Y L hL.normal) Q₁ = Q₁' ∧
      imgOf (psiOf Y L hL.normal) Q₂ = Q₂' ∧ Br2RadY T L Q₁ Q₂ := by
  set ψ := psiOf Y L hL.normal with hψdef
  have hψ : Function.Injective ψ := psiOf_injective hL.core
  have hTY : T ≤ Y := hT.le
  have hLY : L ≤ Y := hL.le
  have hSLY : T ⊓ L ≤ Y := fun x hx => hTY hx.1
  have hS' : imgOf ψ (T ⊓ L) = imgOf ψ T ⊓ innAutOf ↥L := by
    rw [(imgOf_sup_inf hψ hTY hLY).2, imgOf_psiOf_L hL.core]
  obtain ⟨hQ₁'S, hQ₂'S, hgenS, hnorm₁, hnorm₂, helem₁, helem₂, rest⟩ := hrad
  obtain ⟨hcentral, hcover, hrank₁, hrank₂, hgenL, hgenE₁, hgenE₂, hswap⟩ := rest
  have hS'range : imgOf ψ T ⊓ innAutOf ↥L ≤ ψ.range := fun a ha =>
    (imgOf_le_range ψ T) ha.1
  obtain ⟨Q₁, hQ₁Y, hQ₁'im⟩ := exists_eq_imgOf ψ (hQ₁'S.trans hS'range)
  obtain ⟨Q₂, hQ₂Y, hQ₂'im⟩ := exists_eq_imgOf ψ (hQ₂'S.trans hS'range)
  have hQ₁S : Q₁ ≤ T ⊓ L := by
    rw [← imgOf_le_iff hψ hQ₁Y hSLY, hQ₁'im, hS']
    exact hQ₁'S
  have hQ₂S : Q₂ ≤ T ⊓ L := by
    rw [← imgOf_le_iff hψ hQ₂Y hSLY, hQ₂'im, hS']
    exact hQ₂'S
  refine ⟨Q₁, Q₂, hQ₁'im, hQ₂'im, ?_⟩
  refine ⟨hQ₁S, hQ₂S, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← imgOf_le_iff hψ hSLY (sup_le hQ₁Y hQ₂Y), hS',
      (imgOf_sup_inf hψ hQ₁Y hQ₂Y).1, hQ₁'im, hQ₂'im]
    exact hgenS
  · rw [← imgOf_normalizer_le_iff hψ hSLY hQ₁Y, hS', hQ₁'im]
    exact hnorm₁
  · rw [← imgOf_normalizer_le_iff hψ hSLY hQ₂Y, hS', hQ₂'im]
    exact hnorm₂
  · rw [← imgOf_isElemAbelian_iff hψ hQ₁Y, hQ₁'im]
    exact helem₁
  · rw [← imgOf_isElemAbelian_iff hψ hQ₂Y, hQ₂'im]
    exact helem₂
  · intro x hx s hs
    have hxY : x ∈ Y := hSLY (hQ₁S hx.1)
    have hsY : s ∈ Y := hSLY hs
    have hxψ : ψ ⟨x, hxY⟩ ∈ Q₁' ⊓ Q₂' :=
      ⟨by rw [← hQ₁'im]; exact apply_mem_imgOf ψ hx.1 hxY,
       by rw [← hQ₂'im]; exact apply_mem_imgOf ψ hx.2 hxY⟩
    have hsψ : ψ ⟨s, hsY⟩ ∈ imgOf ψ T ⊓ innAutOf ↥L := by
      rw [← hS']
      exact apply_mem_imgOf ψ hs hsY
    have hcomm := hcentral (ψ ⟨x, hxY⟩) hxψ (ψ ⟨s, hsY⟩) hsψ
    have hxs : (⟨x * s, Y.mul_mem hxY hsY⟩ : ↥Y) = ⟨x, hxY⟩ * ⟨s, hsY⟩ := rfl
    have hsx : (⟨s * x, Y.mul_mem hsY hxY⟩ : ↥Y) = ⟨s, hsY⟩ * ⟨x, hxY⟩ := rfl
    have h : (⟨x * s, Y.mul_mem hxY hsY⟩ : ↥Y) = ⟨s * x, Y.mul_mem hsY hxY⟩ := by
      apply hψ
      rw [hxs, hsx, map_mul, map_mul]
      exact hcomm
    exact congrArg (Subtype.val : ↥Y → LGL 2 V) h
  · intro E hE hEe
    have hEY : E ≤ Y := fun x hx => hSLY (hE hx)
    have himgE : imgOf ψ E ≤ imgOf ψ T ⊓ innAutOf ↥L := by
      rw [← hS']
      exact imgOf_mono ψ hE
    have hE'e : IsElemAbelian 2 (imgOf ψ E) := (imgOf_isElemAbelian_iff hψ hEY).mpr hEe
    rcases hcover (imgOf ψ E) himgE hE'e with h | h
    · left; rw [← imgOf_le_iff hψ hEY hQ₁Y, hQ₁'im]; exact h
    · right; rw [← imgOf_le_iff hψ hEY hQ₂Y, hQ₂'im]; exact h
  · intro E hEQ₁
    have hEY : E ≤ Y := hEQ₁.trans hQ₁Y
    have hE'Q : imgOf ψ E ≤ Q₁' := by rw [← hQ₁'im]; exact imgOf_mono ψ hEQ₁
    have hres := hrank₁ (imgOf ψ E) hE'Q
    have hinf : imgOf ψ (E ⊓ Q₂) = imgOf ψ E ⊓ Q₂' := by
      rw [(imgOf_sup_inf hψ hEY hQ₂Y).2, hQ₂'im]
    rw [mOf_eq_mOfG, ← imgOf_mOfG hψ hEY inf_le_left, hinf]
    exact hres
  · intro E hEQ₂
    have hEY : E ≤ Y := hEQ₂.trans hQ₂Y
    have hE'Q : imgOf ψ E ≤ Q₂' := by rw [← hQ₂'im]; exact imgOf_mono ψ hEQ₂
    have hres := hrank₂ (imgOf ψ E) hE'Q
    have hinf : imgOf ψ (E ⊓ Q₁) = imgOf ψ E ⊓ Q₁' := by
      rw [(imgOf_sup_inf hψ hEY hQ₁Y).2, hQ₁'im]
    rw [mOf_eq_mOfG, ← imgOf_mOfG hψ hEY inf_le_left, hinf]
    exact hres
  · have hA₁Y : (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₁ : Set (LGL 2 V)), cj p (T ⊓ L)) ≤ Y :=
      iSup_le fun p => iSup_le fun hp => w183b2_cj_le (hL.le hp.1) hSLY
    have hA₂Y : (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₂ : Set (LGL 2 V)), cj p (T ⊓ L)) ≤ Y :=
      iSup_le fun p => iSup_le fun hp => w183b2_cj_le (hL.le hp.1) hSLY
    apply (w183b2_imgOf_eq_iff hψ (sup_le hA₁Y hA₂Y) hLY).mp
    rw [(imgOf_sup_inf hψ hA₁Y hA₂Y).1]
    rw [show imgOf ψ (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₁ : Set (LGL 2 V)),
          cj p (T ⊓ L)) = ⨆ q ∈ innAutOf ↥L ⊓ Subgroup.normalizer
            (imgOf ψ Q₁ : Set (MulAut ↥L)), autConj q (imgOf ψ (T ⊓ L)) from
        w183b2_imgOf_gen_sup hL.core hSLY hQ₁Y]
    rw [show imgOf ψ (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₂ : Set (LGL 2 V)),
          cj p (T ⊓ L)) = ⨆ q ∈ innAutOf ↥L ⊓ Subgroup.normalizer
            (imgOf ψ Q₂ : Set (MulAut ↥L)), autConj q (imgOf ψ (T ⊓ L)) from
        w183b2_imgOf_gen_sup hL.core hSLY hQ₂Y]
    rw [hQ₁'im, hQ₂'im, hS', imgOf_psiOf_L hL.core]
    exact hgenL
  · intro E hEQ₁ hcard hnE
    have hEY : E ≤ Y := hEQ₁.trans hQ₁Y
    have hE'Q : imgOf ψ E ≤ Q₁' := by rw [← hQ₁'im]; exact imgOf_mono ψ hEQ₁
    have hcard' : 8 ≤ Nat.card (imgOf ψ E) := by
      rw [imgOf_card hψ hEY]; exact hcard
    have hnE' : ¬ imgOf ψ E ≤ Q₁' ⊓ Q₂' := by
      intro h
      apply hnE
      rw [← imgOf_le_iff hψ hEY (inf_le_left.trans hQ₁Y),
        (imgOf_sup_inf hψ hQ₁Y hQ₂Y).2, hQ₁'im, hQ₂'im]
      exact h
    have hres := hgenE₁ (imgOf ψ E) hE'Q hcard' hnE'
    have hA₁Y : (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₁ : Set (LGL 2 V)), cj p E) ≤ Y :=
      iSup_le fun p => iSup_le fun hp => w183b2_cj_le (hL.le hp.1) hEY
    have hgoal : imgOf ψ (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₁ : Set (LGL 2 V)), cj p E) =
        Q₁' := by
      rw [show imgOf ψ (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₁ : Set (LGL 2 V)), cj p E) =
          ⨆ q ∈ innAutOf ↥L ⊓ Subgroup.normalizer (imgOf ψ Q₁ : Set (MulAut ↥L)),
            autConj q (imgOf ψ E) from w183b2_imgOf_gen_sup hL.core hEY hQ₁Y]
      rw [hQ₁'im]
      exact hres
    exact (w183b2_imgOf_eq_iff hψ hA₁Y hQ₁Y).mp (hgoal.trans hQ₁'im.symm)
  · intro E hEQ₂ hcard hnE
    have hEY : E ≤ Y := hEQ₂.trans hQ₂Y
    have hE'Q : imgOf ψ E ≤ Q₂' := by rw [← hQ₂'im]; exact imgOf_mono ψ hEQ₂
    have hcard' : 8 ≤ Nat.card (imgOf ψ E) := by
      rw [imgOf_card hψ hEY]; exact hcard
    have hnE' : ¬ imgOf ψ E ≤ Q₁' ⊓ Q₂' := by
      intro h
      apply hnE
      rw [← imgOf_le_iff hψ hEY (inf_le_right.trans hQ₂Y),
        (imgOf_sup_inf hψ hQ₁Y hQ₂Y).2, hQ₁'im, hQ₂'im]
      exact h
    have hres := hgenE₂ (imgOf ψ E) hE'Q hcard' hnE'
    have hA₂Y : (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₂ : Set (LGL 2 V)), cj p E) ≤ Y :=
      iSup_le fun p => iSup_le fun hp => w183b2_cj_le (hL.le hp.1) hEY
    have hgoal : imgOf ψ (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₂ : Set (LGL 2 V)), cj p E) =
        Q₂' := by
      rw [show imgOf ψ (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₂ : Set (LGL 2 V)), cj p E) =
          ⨆ q ∈ innAutOf ↥L ⊓ Subgroup.normalizer (imgOf ψ Q₂ : Set (MulAut ↥L)),
            autConj q (imgOf ψ E) from w183b2_imgOf_gen_sup hL.core hEY hQ₂Y]
      rw [hQ₂'im]
      exact hres
    exact (w183b2_imgOf_eq_iff hψ hA₂Y hQ₂Y).mp (hgoal.trans hQ₂'im.symm)
  · obtain ⟨τ, hτT, hτdyn⟩ := hL.dynkin
    have hτY : τ ∈ Y := hTY hτT
    have hτNT : τ ∈ Subgroup.normalizer (T ⊓ L : Set (LGL 2 V)) :=
      w183b2_le_normalizer_inf hTY hLY hL.normal hτT
    have hτN : ψ ⟨τ, hτY⟩ ∈ Subgroup.normalizer
        (imgOf ψ T ⊓ innAutOf ↥L : Set (MulAut ↥L)) := by
      have h := (w183b2_mem_normalizer_imgOf_iff hψ hSLY hτY).mpr hτNT
      rwa [hS'] at h
    have hτdyn' : ActsOnDynkinMod ⊥ (innAutOf ↥L) (ψ ⟨τ, hτY⟩) :=
      psiOf_dynkin hL.core hτY hτdyn
    obtain ⟨hsw₁, hsw₂⟩ := hswap (ψ ⟨τ, hτY⟩) hτN hτdyn'
    refine ⟨τ, hτT, ?_, ?_⟩
    · apply (w183b2_imgOf_eq_iff hψ (w183b2_cj_le hτY hQ₁Y) hQ₂Y).mp
      rw [imgOf_cj ψ hQ₁Y hτY, hQ₁'im]
      change autConj (ψ ⟨τ, hτY⟩) Q₁' = imgOf ψ Q₂
      rw [hsw₁, ← hQ₂'im]
    · apply (w183b2_imgOf_eq_iff hψ (w183b2_cj_le hτY hQ₂Y) hQ₁Y).mp
      rw [imgOf_cj ψ hQ₂Y hτY, hQ₂'im]
      change autConj (ψ ⟨τ, hτY⟩) Q₂' = imgOf ψ Q₁
      rw [hsw₂, ← hQ₁'im]

theorem br2_false_of_one_Sp44 (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (hL : Br2OneComp Y T L)
    (hshape : IsSp4 ↥L 2) (hrk : ∀ D ∈ Γ, 3 ≤ mRank D) (hne : Γ.Nonempty)
    (hPT : PairTest Y Γ) (hfin : FinG45Sp44) : False := by
  set ψ := psiOf Y L hL.normal with hψdef
  have hψ : Function.Injective ψ := psiOf_injective hL.core
  have hTY : T ≤ Y := hc.sylow.le
  have hLY : L ≤ Y := hL.le
  have hSLY : T ⊓ L ≤ Y := fun x hx => hTY hx.1
  have hS' : imgOf ψ (T ⊓ L) = imgOf ψ T ⊓ innAutOf ↥L := by
    rw [(imgOf_sup_inf hψ hTY hLY).2, imgOf_psiOf_L hL.core]
  obtain ⟨hgen, hP⟩ := hfin ↥L hshape
  obtain ⟨τ, hτT, hτdyn⟩ := hL.dynkin
  have hτdyn' : ActsOnDynkinMod ⊥ (innAutOf ↥L) (ψ ⟨τ, hTY hτT⟩) :=
    psiOf_dynkin hL.core (hTY hτT) hτdyn
  have hrange : ψ.range = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hgen (ψ ⟨τ, hTY hτT⟩) hτdyn']
    refine sup_le ?_ ?_
    · rw [← imgOf_psiOf_L hL.core]
      exact imgOf_le_range ψ L
    · exact Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨⟨τ, hTY hτT⟩, rfl⟩)
  have hPsylow : IsSylowIn 2 (imgOf ψ T) ⊤ := by
    have h := isSylowIn_imgOf hψ hc.sylow
    rwa [hrange] at h
  obtain ⟨Q₁', Q₂', hrad, hcases⟩ := hP (imgOf ψ T) hPsylow
  have hD3 : ∀ D ∈ Γ, imgOf ψ D ≤ innAutOf ↥L ∧ ∃ g : MulAut ↥L,
      autConj g (imgOf ψ D) ≤ imgOf ψ T ⊓ innAutOf ↥L ∧
      ¬ autConj g (imgOf ψ D) ≤ Q₁' ⊓ Q₂' := by
    intro D hD
    have hDe : IsElemAbelian 2 D := hc.h131.isElemAb D hD
    have hDcard : 8 ≤ Nat.card D := by
      have h3 : 3 ≤ Nat.log 2 (Nat.card D) := hrk D hD
      have hne0 : Nat.card D ≠ 0 := by
        rintro h0
        rw [h0, Nat.log_zero_right] at h3
        omega
      have := Nat.pow_le_of_le_log (b := 2) (x := 3) (y := Nat.card D) hne0 h3
      simpa using this
    have hD'e : IsElemAbelian 2 (imgOf ψ D) :=
      (imgOf_isElemAbelian_iff hψ (hc.h131.le_G D hD)).mpr hDe
    have hD'card : 8 ≤ Nat.card (imgOf ψ D) := by
      rw [imgOf_card hψ (hc.h131.le_G D hD)]; exact hDcard
    rcases hcases (imgOf ψ D) hD'e hD'card with hpair | hsecond | hthird
    · obtain ⟨y', hpair⟩ := hpair
      have hy'mem : y' ∈ ψ.range := by rw [hrange]; exact Subgroup.mem_top y'
      obtain ⟨y₀, hy₀⟩ := MonoidHom.mem_range.mp hy'mem
      have hpair' : PairViolation (imgOf ψ D) (ψ y₀) := by rw [hy₀]; exact hpair
      exact absurd (pairViolation_of_imgOf hψ (hc.h131.le_G D hD) y₀.2 hpair')
        (hPT D hD y₀ y₀.2)
    · obtain ⟨g, hgP, hinv, hN⟩ := hsecond
      exact absurd (w183b2_sp44_no_r2 hc.toBr1Base hL hrange hD hgP hinv hN) not_false
    · exact hthird
  obtain ⟨Q₁, Q₂, hQ₁'im, hQ₂'im, hR⟩ := br2RadY_of_two_radicals hc.sylow hL hrad
  have hQ₁Y : Q₁ ≤ Y := hR.le₁.trans hSLY
  have hQ₂Y : Q₂ ≤ Y := hR.le₂.trans hSLY
  have hgenQ : ∀ B ∈ 𝒢, B ≤ Q₁ ∨ B ≤ Q₂ := by
    intro B hB
    obtain ⟨hBT, D', hD', hBD', _⟩ := hc.gens B hB
    have hBY : B ≤ Y := fun b hb => hTY (hBT hb)
    have hBin : imgOf ψ B ≤ innAutOf ↥L := (imgOf_mono ψ hBD').trans (hD3 D' hD').1
    have hB'S : imgOf ψ B ≤ imgOf ψ (T ⊓ L) := by
      rw [hS']
      exact fun x hx => ⟨imgOf_mono ψ hBT hx, hBin hx⟩
    have hBS : B ≤ T ⊓ L := (imgOf_le_iff hψ hBY hSLY).mp hB'S
    have hBe : IsElemAbelian 2 B :=
      w183b2_isElemAbelian_of_le (hc.h131.isElemAb D' hD') hBD'
    exact hR.cover B hBS hBe
  obtain ⟨D₀, hD₀⟩ := hne
  obtain ⟨-, hD₀ex⟩ := hD3 D₀ hD₀
  obtain ⟨g, hgP, hgZ⟩ := hD₀ex
  have hgmem : g ∈ ψ.range := by rw [hrange]; exact Subgroup.mem_top g
  obtain ⟨y, hyg⟩ := MonoidHom.mem_range.mp hgmem
  have hD₁ : cj (y : LGL 2 V) D₀ ∈ Γ := hc.h131.invariant D₀ hD₀ (y : LGL 2 V) y.2
  have hD₁Y : cj (y : LGL 2 V) D₀ ≤ Y := hc.h131.le_G _ hD₁
  have him : imgOf ψ (cj (y : LGL 2 V) D₀) = autConj (ψ y) (imgOf ψ D₀) :=
    imgOf_cj ψ (hc.h131.le_G D₀ hD₀) y.2
  have hD₁S : cj (y : LGL 2 V) D₀ ≤ T ⊓ L := by
    rw [← imgOf_le_iff hψ hD₁Y hSLY, him, hyg, hS']
    exact hgP
  have hD₁Z : ¬ cj (y : LGL 2 V) D₀ ≤ Q₁ ⊓ Q₂ := by
    intro h
    apply hgZ
    have hle : imgOf ψ (cj (y : LGL 2 V) D₀) ≤ imgOf ψ (Q₁ ⊓ Q₂) :=
      imgOf_mono ψ h
    rw [him] at hle
    rw [show autConj (ψ y) (imgOf ψ D₀) = autConj g (imgOf ψ D₀) from by rw [hyg]] at hle
    rw [(imgOf_sup_inf hψ hQ₁Y hQ₂Y).2, hQ₁'im, hQ₂'im] at hle
    exact hle
  exact br2_false_of_two_radicals hc.toBr1Base hL.core hR hgenQ hrk hD₁ hD₁S hD₁Z

end CFSG.LocalAnalysis.WeakClosure81

end
