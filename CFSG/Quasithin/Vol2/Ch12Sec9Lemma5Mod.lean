module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Act

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace L1295A

@[expose] def restr {W : Type*} [Group W] (Y : Subgroup W) (g : MulAut W)
    (h1 : ∀ y ∈ Y, g y ∈ Y) (h2 : ∀ y ∈ Y, g.symm y ∈ Y) : MulAut ↥Y where
  toFun y := ⟨g (y : W), h1 y y.2⟩
  invFun y := ⟨g.symm (y : W), h2 y y.2⟩
  left_inv y := Subtype.ext (g.symm_apply_apply (y : W))
  right_inv y := Subtype.ext (g.apply_symm_apply (y : W))
  map_mul' a b := Subtype.ext (map_mul g (a : W) (b : W))

theorem restr_apply {W : Type*} [Group W] (Y : Subgroup W) (g : MulAut W)
    (h1 : ∀ y ∈ Y, g y ∈ Y) (h2 : ∀ y ∈ Y, g.symm y ∈ Y) (y : Y) :
    ((restr Y g h1 h2 y : ↥Y) : W) = g (y : W) := rfl

theorem card_quotient_le_of_le {Γ : Type*} [Group Γ] [Finite Γ] {K P : Subgroup Γ}
    (hKP : K ≤ P) : Nat.card (Γ ⧸ P) ≤ Nat.card (Γ ⧸ K) :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := K)))
    (Subgroup.index_dvd_of_le hKP)

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {n : ℕ} {V₁ H₁ : Subgroup G}

abbrev Yg (L V V₁ H₁ : Subgroup G) :
    Subgroup ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) :=
  (tildeOf V₁ V).subgroupOf _

omit [Finite G] in
theorem tildeV_le : tildeOf V₁ V ≤ tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)) :=
  secImg_mono (le_conjClosure V _)

abbrev Am.Cs (A : Am G T L V n V₁ H₁) :
    Subgroup (MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) :=
  Subgroup.centralizer (A.Ls : Set (MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))))

namespace Am

variable (A : Am G T L V n V₁ H₁)
include A

theorem card_tildeV : Nat.card (tildeOf V₁ V) = 2 ^ (n - 1) := by
  obtain ⟨hcard, -, -⟩ := A.cx.hyp.card_sq
  have hVN : V ≤ Subgroup.normalizer (V₁ : Set G) := A.V_le_T.trans A.v1.2.2
  have h1 := relIndex_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) le_rfl A.v1.1 hVN
  have hbot : secImg (Subgroup.normalizer (V₁ : Set G)) V₁ V₁ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_secImg.1 hy
    exact secMk_eq_one_iff.2 hx
  rw [hbot, Subgroup.relIndex_bot_left] at h1
  have h2 := Subgroup.relIndex_mul_card V₁ V
  rw [inf_eq_left.2 A.v1.1, A.v1.2.1, hcard] at h2
  have hn : 1 ≤ n := by rcases A.cx.n45 with h | h <;> omega
  have h3 : 2 ^ n = 2 ^ (n - 1) * 2 ^ 1 := by
    rw [← pow_add]
    congr 1
    omega
  rw [h3] at h2
  show Nat.card (secImg _ V₁ V) = _
  rw [h1]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2

theorem card_Yg : Nat.card (Yg L V V₁ H₁) = 2 ^ (n - 1) :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe tildeV_le).toEquiv).trans A.card_tildeV

theorem mapsTo_Yg {g : MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))} (hg : g ∈ A.Ls)
    {y : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))} (hy : y ∈ Yg L V V₁ H₁) :
    g y ∈ Yg L V V₁ H₁ := by
  obtain ⟨⟨l, hlH⟩, hl, rfl⟩ := hg
  have hl' : l ∈ lOne L V₁ := hl
  have hlV : l ∈ Subgroup.normalizer (V : Set G) :=
    A.cx.hyp.hyp.irrPlus.2.2.1 (((oTwoUpper_le _).trans inf_le_left) hl')
  rw [Subgroup.mem_subgroupOf] at hy ⊢
  rw [rho_apply]
  exact secMk_conj_mem_secImg hlV hy

theorem mapsTo_Yg_symm {g : MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))}
    (hg : g ∈ A.Ls) {y : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))}
    (hy : y ∈ Yg L V V₁ H₁) : g.symm y ∈ Yg L V V₁ H₁ :=
  A.mapsTo_Yg (Subgroup.inv_mem _ hg) hy

theorem map_Yg {g : MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))} (hg : g ∈ A.Ls) :
    (Yg L V V₁ H₁).map g.toMonoidHom = Yg L V V₁ H₁ := by
  refine le_antisymm ?_ fun y hy => ⟨g.symm y, A.mapsTo_Yg_symm hg hy, g.apply_symm_apply y⟩
  rintro _ ⟨y, hy, rfl⟩
  exact A.mapsTo_Yg hg hy

theorem onto_Yg (τ : MulAut ↥(Yg L V V₁ H₁)) :
    ∃ g ∈ A.Ls, ∀ y : Yg L V V₁ H₁, g (y : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) =
      (τ y : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) := by
  classical
  have hn : n ≠ 3 := by rcases A.cx.n45 with h | h <;> omega
  have hn1 : 1 ≤ n - 1 := by rcases A.cx.n45 with h | h <;> omega
  have hlLs : ∀ l : ↥(lOne L V₁), A.rho ⟨l, Subgroup.mem_sup_right l.2⟩ ∈ A.Ls :=
    fun l => ⟨⟨l, Subgroup.mem_sup_right l.2⟩, l.2, rfl⟩
  let ψ : ↥(lOne L V₁) →* MulAut ↥(Yg L V V₁ H₁) :=
    { toFun := fun l => restr _ (A.rho ⟨l, Subgroup.mem_sup_right l.2⟩)
        (fun y hy => A.mapsTo_Yg (hlLs l) hy) (fun y hy => A.mapsTo_Yg_symm (hlLs l) hy)
      map_one' := by
        refine MulEquiv.ext fun y => Subtype.ext ?_
        rw [restr_apply]
        have : (⟨((1 : ↥(lOne L V₁)) : G), Subgroup.mem_sup_right (1 : ↥(lOne L V₁)).2⟩ :
          ↥(H₁ ⊔ lOne L V₁)) = 1 := rfl
        rw [this, map_one]
        rfl
      map_mul' := fun a b => by
        refine MulEquiv.ext fun y => Subtype.ext ?_
        rw [restr_apply]
        have : (⟨((a * b : ↥(lOne L V₁)) : G), Subgroup.mem_sup_right (a * b).2⟩ :
            ↥(H₁ ⊔ lOne L V₁)) =
              ⟨a, Subgroup.mem_sup_right a.2⟩ * ⟨b, Subgroup.mem_sup_right b.2⟩ := rfl
        rw [this, map_mul]
        rfl }
  have hψ : ∀ l y, ((ψ l y : ↥(Yg L V V₁ H₁)) : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) =
      A.rho ⟨l, Subgroup.mem_sup_right l.2⟩ y := fun _ _ => rfl
  obtain ⟨Q, _, ρX, -, hker, htriv, -⟩ := exists_lOne_rep A.h1222 A.cx.hyp hn A.v1
  have hkerle : ψ.ker ≤ CFSG.pCore 2 ↥(lOne L V₁) := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have hV : ∀ v ∈ V, (l : G) * v * (l : G)⁻¹ * v⁻¹ ∈ V₁ := by
      intro v hv
      have hvU : v ∈ conjClosure V (H₁ ⊔ lOne L V₁) := le_conjClosure V _ hv
      have hvY : A.uMk hvU ∈ Yg L V V₁ H₁ := by
        rw [Subgroup.mem_subgroupOf]
        exact secMk_mem_secImg hv
      have h1 := congrArg (fun f : MulAut ↥(Yg L V V₁ H₁) =>
        ((f ⟨_, hvY⟩ : ↥(Yg L V V₁ H₁)) : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))))) hl
      simp only [hψ, MulAut.one_apply] at h1
      exact (A.rho_uMk_eq_iff _ hvU).1 h1
    have h2 := htriv ⟨l, (oTwoUpper_le _) l.2⟩ hV
    rw [← hker]
    exact h2
  obtain ⟨e⟩ := lOne_quotient_mulEquiv A.h1222 A.cx.hyp hn A.v1
  have hcomm : IsMulCommutative ↥(Yg L V V₁ H₁) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (by
      have := A.elemAb.1
      exact setLike_mul_comm (a : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))).2
        (b : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))).2))⟩⟩
  have hsq : ∀ v ∈ Yg L V V₁ H₁, v ^ 2 = 1 := fun v _ =>
    Subtype.ext (by simpa using A.elemAb.2 v v.2)
  have h1 := card_mulAut_le hsq A.card_Yg hn1
  have h2 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := ZMod 2) hn1
  rw [Nat.card_zmod] at h2
  have h3 : Nat.card (MulAut ↥(Yg L V V₁ H₁)) ≤ Nat.card ψ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    calc Nat.card (MulAut ↥(Yg L V V₁ H₁)) ≤ _ := h1
      _ = Nat.card (Matrix.SpecialLinearGroup (Fin (n - 1)) (ZMod 2)) := h2.symm
      _ = Nat.card (↥(lOne L V₁) ⧸ CFSG.pCore 2 ↥(lOne L V₁)) := (Nat.card_congr e.toEquiv).symm
      _ ≤ Nat.card (↥(lOne L V₁) ⧸ ψ.ker) := card_quotient_le_of_le hkerle
  have htop : ψ.range = ⊤ := Subgroup.eq_top_of_le_card _ h3
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.1 (htop ▸ Subgroup.mem_top τ)
  refine ⟨_, hlLs l, fun y => ?_⟩
  rw [← hl]
  rfl

theorem map_span_le {f : MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))}
    (hf : f ∈ A.Cs ⊔ A.Ls) :
    (⨆ c ∈ A.Cs, (Yg L V V₁ H₁).map c.toMonoidHom).map
        f.toMonoidHom ≤
      ⨆ c ∈ A.Cs, (Yg L V V₁ H₁).map c.toMonoidHom := by
  set S := ⨆ c ∈ A.Cs, (Yg L V V₁ H₁).map c.toMonoidHom with hS
  have hmapmul : ∀ (a b : MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))),
      ((Yg L V V₁ H₁).map b.toMonoidHom).map a.toMonoidHom =
        (Yg L V V₁ H₁).map (a * b).toMonoidHom := by
    intro a b
    rw [Subgroup.map_map]
    rfl
  have hC : ∀ g ∈ A.Cs, S.map g.toMonoidHom ≤ S := by
    intro g hg
    rw [Subgroup.map_le_iff_le_comap, hS]
    refine iSup₂_le fun c hc => ?_
    rw [← Subgroup.map_le_iff_le_comap, hmapmul]
    exact le_iSup₂ (f := fun c (_ : c ∈ A.Cs) =>
      (Yg L V V₁ H₁).map c.toMonoidHom) _ (Subgroup.mul_mem _ hg hc)
  have hL : ∀ g ∈ A.Ls, S.map g.toMonoidHom ≤ S := by
    intro g hg
    rw [Subgroup.map_le_iff_le_comap, hS]
    refine iSup₂_le fun c hc => ?_
    rw [← Subgroup.map_le_iff_le_comap, hmapmul, Subgroup.mem_centralizer_iff.1 hc g hg,
      ← hmapmul, A.map_Yg hg]
    exact le_iSup₂ (f := fun c (_ : c ∈ A.Cs) =>
      (Yg L V V₁ H₁).map c.toMonoidHom) c hc
  have hle : A.Cs ≤
      Subgroup.normalizer (A.Ls : Set (MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))))) :=
    Subgroup.centralizer_le_normalizer _
  have hf' : f ∈ ((A.Cs ⊔ A.Ls : Subgroup _) :
      Set (MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))))) := hf
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hf'
  obtain ⟨c', hc', l', hl', rfl⟩ := hf'
  have e : S.map (c' * l').toMonoidHom = (S.map l'.toMonoidHom).map c'.toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [e]
  exact (Subgroup.map_mono (hL l' hl')).trans (hC c' hc')

theorem span_eq_top :
    ⨆ c ∈ A.Cs, (Yg L V V₁ H₁).map c.toMonoidHom = ⊤ := by
  obtain ⟨S, hS⟩ : ∃ S, S = ⨆ c ∈ A.Cs, (Yg L V V₁ H₁).map c.toMonoidHom := ⟨_, rfl⟩
  rw [← hS]
  have hSinv : ∀ f ∈ A.Cs ⊔ A.Ls, S.map f.toMonoidHom ≤ S := fun f hf => by
    rw [hS]
    exact A.map_span_le hf
  have hYS : Yg L V V₁ H₁ ≤ S := by
    have h1 : (Yg L V V₁ H₁).map
        (1 : MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))).toMonoidHom ≤ S := by
      rw [hS]
      exact le_iSup₂ (f := fun c (_ : c ∈ A.Cs) => (Yg L V V₁ H₁).map c.toMonoidHom) 1
        (Subgroup.one_mem _)
    have h2 : (Yg L V V₁ H₁).map
        (1 : MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))).toMonoidHom =
          Yg L V V₁ H₁ := by
      have : (1 : MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))).toMonoidHom =
        MonoidHom.id _ := rfl
      rw [this, Subgroup.map_id]
    rwa [h2] at h1
  have hconj : ∀ x : ↥(Subgroup.normalizer (V₁ : Set G)), (x : G) ∈ H₁ ⊔ lOne L V₁ →
      ∀ y ∈ S.map (tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))).subtype,
        secMk _ V₁ x * y * (secMk _ V₁ x)⁻¹ ∈
          S.map (tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))).subtype := by
    rintro x hx _ ⟨s, hs, rfl⟩
    refine ⟨A.rho ⟨x, hx⟩ s, hSinv _ (A.rho_mem_sup ⟨x, hx⟩) ⟨s, hs, rfl⟩, ?_⟩
    show ((A.rho ⟨x, hx⟩ s : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) :
      SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) = _
    rw [rho_apply]
    rfl
  have hle : tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)) ≤
      S.map (tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))).subtype := by
    refine secImg_conjClosure_le A.le_normalizer (A.V_le_T.trans A.v1.2.2) (fun x hx => ?_) ?_
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => hconj x hx y hy, fun hy => ?_⟩
      have h1 := hconj x⁻¹ (Subgroup.inv_mem _ hx) _ hy
      rwa [map_inv, inv_inv, show (secMk _ V₁ x)⁻¹ * (secMk _ V₁ x * y * (secMk _ V₁ x)⁻¹) *
        secMk _ V₁ x = y by group] at h1
    · intro y hy
      refine ⟨⟨y, tildeV_le hy⟩, hYS ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact hy
  rw [eq_top_iff]
  intro u _
  obtain ⟨s, hs, hsu⟩ := hle u.2
  have : s = u := Subtype.ext hsu
  rw [← this]
  exact hs

end Am

end L1295A

end CFSG.Quasithin.H13
