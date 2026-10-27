module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeModBlock
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_mem_map_of_map_inv_eq {W : Type*} [Group W] (f : MulAut W)
    {J K : Subgroup W} (h : J.map (f⁻¹).toMonoidHom = K) :
    ∀ w ∈ K, f w ∈ J := by
  intro w hw
  rw [← h] at hw
  obtain ⟨x, hx, hxw⟩ := Subgroup.mem_map.1 hw
  have hfx : f w = x := by
    rw [← hxw]
    exact MulAut.apply_inv_self (M := W) f x
  rwa [hfx]

private theorem c23ne_map_conj_barSub {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ stabTil V₀ V) {K A B : Subgroup G}
    (hK : conjSubgroup K m = B) (hA : barSub V₀ V hV K = barSub V₀ V hV A) :
    (barSub V₀ V hV A).map (MulAut.conj (actTil V₀ V hV ⟨m, hm⟩)⁻¹).toMonoidHom =
      barSub V₀ V hV B := by
  rw [← hA, ← s15_Infra_barSub_conjSubgroup V₀ V hV hm K, hK]

private theorem c23ne_wTil_map_conj {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ stabTil V₀ V) {A A' : Subgroup G}
    (h : (barSub V₀ V hV A).map
      (MulAut.conj (actTil V₀ V hV ⟨m, hm⟩)⁻¹).toMonoidHom = barSub V₀ V hV A') :
    (wTil V₀ V hV A).map ((actTil V₀ V hV ⟨m, hm⟩)⁻¹).toMonoidHom = wTil V₀ V hV A' := by
  unfold wTil
  rw [← h, s15_Infra_commSub_top_map_conj]

private theorem c23ne_mem_normalizer_of_conj {Y V : Subgroup G} (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ stabTil Y V) {K : Subgroup G} (hK : conjSubgroup K m = K) :
    actTil Y V hV ⟨m, hm⟩ ∈
      Subgroup.normalizer (barSub Y V hV K : Set (MulAut (Vtil Y V hV))) := by
  have hh := s15_Infra_barSub_conjSubgroup Y V hV hm K
  rw [hK] at hh
  have hinv : (actTil Y V hV ⟨m, hm⟩)⁻¹ ∈
      Subgroup.normalizer (barSub Y V hV K : Set (MulAut (Vtil Y V hV))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa using hh.symm
  simpa using (Subgroup.normalizer (barSub Y V hV K :
    Set (MulAut (Vtil Y V hV)))).inv_mem hinv

private theorem c23ne_pBlock_map_of_map {Y V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hY : Y ≤ V₀) {A A' : Subgroup (Vtil V₀ V hV)} {m : MulAut (Vtil Y V hV)}
    {m₀ : MulAut (Vtil V₀ V hV)}
    (hproj : ∀ q, c23neProj Y V₀ V hV hY (m q) = m₀ (c23neProj Y V₀ V hV hY q))
    (hmap : ∀ w ∈ A, m₀ w ∈ A') :
    ∀ e ∈ c23nePBlock Y V₀ V hV hY A, m e ∈ c23nePBlock Y V₀ V hV hY A' := by
  intro e he
  have he' : c23neProj Y V₀ V hV hY e ∈ A := (c23ne_mem_pBlock_iff hV hY A e).1 he
  rw [c23ne_mem_pBlock_iff hV hY A']
  rw [hproj]
  exact hmap _ he'

theorem c23ne_pBlock_sup {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L) ⊔
      c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV (conjSubgroup L x)) = ⊤ := by
  unfold c23nePBlock
  rw [Subgroup.comap_sup_eq (c23neProj (c23neY V K₁ K₂) V₀ V hV h.Y_le)
    (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x))
    (c23neProj_surjective hV h.Y_le), h.ctx.core.sup_eq, Subgroup.comap_top]

theorem c23ne_pBlock_inf {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L) ⊓
      c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV (conjSubgroup L x)) ≤
        imgTil (c23neY V K₁ K₂) V hV V₀ := by
  intro q hq
  rw [Subgroup.mem_inf] at hq
  rw [← c23neProj_ker hV h.Y_le, MonoidHom.mem_ker]
  have h1 : c23neProj (c23neY V K₁ K₂) V₀ V hV h.Y_le q ∈ wTil V₀ V hV L :=
    (c23ne_mem_pBlock_iff hV h.Y_le _ q).1 hq.1
  have h2 : c23neProj (c23neY V K₁ K₂) V₀ V hV h.Y_le q ∈
      wTil V₀ V hV (conjSubgroup L x) :=
    (c23ne_mem_pBlock_iff hV h.Y_le _ q).1 hq.2
  have h3 : c23neProj (c23neY V K₁ K₂) V₀ V hV h.Y_le q ∈
      wTil V₀ V hV L ⊓ wTil V₀ V hV (conjSubgroup L x) := ⟨h1, h2⟩
  rw [h.ctx.core.inf_eq, Subgroup.mem_bot] at h3
  exact h3

theorem c23ne_modPair_perm {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    ∀ m ∈ barSub (c23neY V K₁ K₂) V hV D.M,
      (m ∈ Subgroup.normalizer (barSub (c23neY V K₁ K₂) V hV K₁ :
          Set (MulAut (Vtil (c23neY V K₁ K₂) V hV))) ∧
        m ∈ Subgroup.normalizer (barSub (c23neY V K₁ K₂) V hV K₂ :
          Set (MulAut (Vtil (c23neY V K₁ K₂) V hV))) ∧
        (∀ e ∈ c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L),
          m e ∈ c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L)) ∧
        (∀ e ∈ c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV (conjSubgroup L x)),
          m e ∈ c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le
            (wTil V₀ V hV (conjSubgroup L x)))) ∨
      ((∀ e ∈ c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L),
          m e ∈ c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le
            (wTil V₀ V hV (conjSubgroup L x))) ∧
        (∀ e ∈ c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV (conjSubgroup L x)),
          m e ∈ c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L))) := by
  set Y : Subgroup G := c23neY V K₁ K₂ with hY
  intro m hm
  obtain ⟨g, hgM, rfl⟩ := (mem_barSub Y V hV D.M m).1 hm
  have hg₀ : (g : G) ∈ stabTil V₀ V := h.stab hgM
  rcases h.ctx.perm (g : G) hgM with ⟨hK₁, hK₂⟩ | ⟨hK₁, hK₂⟩
  · left
    have hnorm₁ : actTil Y V hV g ∈
        Subgroup.normalizer (barSub Y V hV K₁ : Set (MulAut (Vtil Y V hV))) :=
      c23ne_mem_normalizer_of_conj hV g.2 hK₁
    have hnorm₂ : actTil Y V hV g ∈
        Subgroup.normalizer (barSub Y V hV K₂ : Set (MulAut (Vtil Y V hV))) :=
      c23ne_mem_normalizer_of_conj hV g.2 hK₂
    have hbarL : (barSub V₀ V hV L).map
        (MulAut.conj (actTil V₀ V hV ⟨(g : G), hg₀⟩)⁻¹).toMonoidHom = barSub V₀ V hV L :=
      (c23ne_map_conj_barSub hV hg₀ hK₁ h.ctx.bar₁).trans h.ctx.bar₁
    have hbarLx : (barSub V₀ V hV (conjSubgroup L x)).map
        (MulAut.conj (actTil V₀ V hV ⟨(g : G), hg₀⟩)⁻¹).toMonoidHom =
        barSub V₀ V hV (conjSubgroup L x) :=
      (c23ne_map_conj_barSub hV hg₀ hK₂ h.ctx.bar₂).trans h.ctx.bar₂
    have hWmem : ∀ w ∈ wTil V₀ V hV L,
        actTil V₀ V hV ⟨(g : G), hg₀⟩ w ∈ wTil V₀ V hV L :=
      c23ne_mem_map_of_map_inv_eq (actTil V₀ V hV ⟨(g : G), hg₀⟩)
        (c23ne_wTil_map_conj hV hg₀ hbarL)
    have hWxmem : ∀ w ∈ wTil V₀ V hV (conjSubgroup L x),
        actTil V₀ V hV ⟨(g : G), hg₀⟩ w ∈ wTil V₀ V hV (conjSubgroup L x) :=
      c23ne_mem_map_of_map_inv_eq (actTil V₀ V hV ⟨(g : G), hg₀⟩)
        (c23ne_wTil_map_conj hV hg₀ hbarLx)
    refine ⟨hnorm₁, hnorm₂, ?_, ?_⟩
    · exact c23ne_pBlock_map_of_map hV h.Y_le
        (fun q => c23neProj_actTil hV h.Y_le hg₀ g.2 q) hWmem
    · exact c23ne_pBlock_map_of_map hV h.Y_le
        (fun q => c23neProj_actTil hV h.Y_le hg₀ g.2 q) hWxmem
  · right
    have hbarL : (barSub V₀ V hV L).map
        (MulAut.conj (actTil V₀ V hV ⟨(g : G), hg₀⟩)⁻¹).toMonoidHom =
        barSub V₀ V hV (conjSubgroup L x) :=
      (c23ne_map_conj_barSub hV hg₀ hK₁ h.ctx.bar₁).trans h.ctx.bar₂
    have hbarLx : (barSub V₀ V hV (conjSubgroup L x)).map
        (MulAut.conj (actTil V₀ V hV ⟨(g : G), hg₀⟩)⁻¹).toMonoidHom =
        barSub V₀ V hV L :=
      (c23ne_map_conj_barSub hV hg₀ hK₂ h.ctx.bar₂).trans h.ctx.bar₁
    have hW_to_Wx : ∀ w ∈ wTil V₀ V hV L,
        actTil V₀ V hV ⟨(g : G), hg₀⟩ w ∈ wTil V₀ V hV (conjSubgroup L x) :=
      c23ne_mem_map_of_map_inv_eq (actTil V₀ V hV ⟨(g : G), hg₀⟩)
        (c23ne_wTil_map_conj hV hg₀ hbarLx)
    have hWx_to_W : ∀ w ∈ wTil V₀ V hV (conjSubgroup L x),
        actTil V₀ V hV ⟨(g : G), hg₀⟩ w ∈ wTil V₀ V hV L :=
      c23ne_mem_map_of_map_inv_eq (actTil V₀ V hV ⟨(g : G), hg₀⟩)
        (c23ne_wTil_map_conj hV hg₀ hbarL)
    refine ⟨?_, ?_⟩
    · exact c23ne_pBlock_map_of_map hV h.Y_le
        (fun q => c23neProj_actTil hV h.Y_le hg₀ g.2 q) hW_to_Wx
    · exact c23ne_pBlock_map_of_map hV h.Y_le
        (fun q => c23neProj_actTil hV h.Y_le hg₀ g.2 q) hWx_to_W

theorem c23ne_modPair_of_ns {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    C23AModPair (barSub (c23neY V K₁ K₂) V hV D.M)
      (barSub (c23neY V K₁ K₂) V hV K₁) (barSub (c23neY V K₁ K₂) V hV K₂)
      (c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L))
      (c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV (conjSubgroup L x)))
      (c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L) ⊓
        fixV (barSub (c23neY V K₁ K₂) V hV K₁))
      (c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV (conjSubgroup L x)) ⊓
        fixV (barSub (c23neY V K₁ K₂) V hV K₂)) := by
  obtain ⟨hK₂, hP₂⟩ := c23ne_transport h.stab h.ctx h.Y_le h.stabY
  have hblk₁ := c23ne_block₁ h
  have hblk₂ := c23a_block_map hblk₁
    (actTil (c23neY V K₁ K₂) V hV ⟨x, h.stabY h.ctx.hxM⟩)⁻¹
  rw [← hK₂, ← hP₂] at hblk₂
  have hK₁M : K₁ ≤ D.M := uc22p22a_le_of_isSubnormal h.ctx.mem₁.1
  have hK₂M : K₂ ≤ D.M := uc22p22a_le_of_isSubnormal h.ctx.mem₂.1
  have hK₁₀ : K₁ ≤ centralizer (V₀ : Set G) := le_sup_left.trans h.ctx.cent₀
  have hK₂₀ : K₂ ≤ centralizer (V₀ : Set G) := le_sup_right.trans h.ctx.cent₀
  have hfix₁ := c23ne_pBlock_fix_eq h
  have hZ₁ : imgTil (c23neY V K₁ K₂) V hV V₀ ≤
      c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L) ⊓
        fixV (barSub (c23neY V K₁ K₂) V hV K₁) := hfix₁.symm.le
  have hZ₂ : imgTil (c23neY V K₁ K₂) V hV V₀ ≤
      c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV (conjSubgroup L x)) ⊓
        fixV (barSub (c23neY V K₁ K₂) V hV K₂) :=
    le_inf (c23ne_ker_le_pBlock hV h.Y_le _) (c23ne_imgTil_le_fixV hV hK₂₀)
  have hne₁ : c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L) ⊓
      fixV (barSub (c23neY V K₁ K₂) V hV K₁) ≠ ⊥ := by
    intro hb
    rw [hfix₁] at hb
    have hc := c23ne_card_imgTil h
    rw [hb, Subgroup.card_bot] at hc
    omega
  exact
  { exp2 := s15_Infra_vtil_sq_eq_one (c23neY V K₁ K₂) V hV
    blk₁ := hblk₁
    blk₂ := by rw [← hblk₂.fix]; exact hblk₂
    sup := c23ne_pBlock_sup h
    inf₁ := (c23ne_pBlock_inf h).trans hZ₁
    inf₂ := (c23ne_pBlock_inf h).trans hZ₂
    ne₁ := hne₁
    ne₂ := by
      rw [← hblk₂.fix]
      exact fun hb => hne₁ ((Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)).1 hb)
    perm := c23ne_modPair_perm h }

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
