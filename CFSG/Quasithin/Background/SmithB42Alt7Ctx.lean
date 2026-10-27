module

public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Dim

public section

namespace CFSG.Quasithin

namespace B42Alt7

open CFSG.Open CFSG.QuasithinUnique Equiv Equiv.Perm

variable {S : Type} [CommGroup S] {G L : Subgroup (MulAut S)}

theorem nonempty_iso_of_center {X : Type} [Group X] {m : ℕ} (hc : Subgroup.center X = ⊥)
    (h : Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin m))) :
    Nonempty (X ≃* alternatingGroup (Fin m)) := by
  obtain ⟨e⟩ := h
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)).trans
    e⟩

theorem exists_embedding_of [Finite S] {m : ℕ} (hm : 5 ≤ m) (hm6 : m ≠ 6)
    (hF : L = quasithinGenFitting G) (hc : Subgroup.center ↥L = ⊥)
    (ι : ↥L ≃* alternatingGroup (Fin m)) :
    ∃ e : ↥G →* Perm (Fin m), Function.Injective e ∧
      ∀ (l : ↥L) (hl : (l : MulAut S) ∈ G), e ⟨l, hl⟩ = (ι l : Perm (Fin m)) := by
  have hLG : L ≤ G := CFSG.QuasithinUnique.Bridge.FStarSimple.le_G hF
  have hnormal : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := CFSG.QuasithinUnique.Bridge.FStarSimple.normal hF
  have hcent : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g = 1 := CFSG.QuasithinUnique.Bridge.FStarSimple.cent_trivial hF hc
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm hm6
  let Ls : Subgroup ↥G := L.subgroupOf G
  have : Ls.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hnormal g g.2 n hn
    simpa using this⟩
  let φ : ↥Ls ≃* alternatingGroup (Fin m) := (Subgroup.subgroupOfEquivOfLe hLG).trans ι
  let cEquiv : Perm (Fin m) ≃* MulAut (alternatingGroup (Fin m)) := MulEquiv.ofBijective _ hbij
  let ec : ↥G →* MulAut (alternatingGroup (Fin m)) :=
    (MulAut.congr φ).toMonoidHom.comp (MulAut.conjNormal (H := Ls))
  let e : ↥G →* Perm (Fin m) := cEquiv.symm.toMonoidHom.comp ec
  have hce : ∀ g : ↥G, MulAut.conjNormal (e g) = ec g := fun g => by
    show cEquiv (cEquiv.symm (ec g)) = ec g
    exact cEquiv.apply_symm_apply _
  let lsOf : ↥L → ↥Ls := fun l => ⟨⟨(l : MulAut S), hLG l.2⟩, Subgroup.mem_subgroupOf.2 l.2⟩
  have hφl : ∀ l : ↥L, φ (lsOf l) = ι l := fun l => rfl
  have hconj : ∀ (g : ↥G) (x : ↥Ls),
      (φ (MulAut.conjNormal g x) : Perm (Fin m)) = e g * (φ x : Perm (Fin m)) * (e g)⁻¹ := by
    intro g x
    have h1 := congrArg (fun f : MulAut (alternatingGroup (Fin m)) =>
      ((f (φ x) : alternatingGroup (Fin m)) : Perm (Fin m))) (hce g)
    simp only [MulAut.conjNormal_apply] at h1
    rw [h1]
    simp [ec, MulAut.congr_apply]
  have hconjL : ∀ (g : ↥G) (l l' : ↥L),
      (g : MulAut S) * (l : MulAut S) * (g : MulAut S)⁻¹ = (l' : MulAut S) →
        (ι l' : Perm (Fin m)) = e g * (ι l : Perm (Fin m)) * (e g)⁻¹ := by
    intro g l l' hll'
    have h := hconj g (lsOf l)
    have e1 : MulAut.conjNormal g (lsOf l) = lsOf l' := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hll'
    rw [e1, hφl, hφl] at h
    exact h
  have hinj : Function.Injective e := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hcomm : ∀ l ∈ L, (g : MulAut S) * l = l * (g : MulAut S) := by
      intro l hl
      have hl'' : (g : MulAut S) * l * (g : MulAut S)⁻¹ ∈ L := hnormal g g.2 l hl
      have h := hconjL g ⟨l, hl⟩ ⟨_, hl''⟩ rfl
      rw [hg] at h
      simp only [one_mul, inv_one, mul_one] at h
      have h2 : (⟨(g : MulAut S) * l * (g : MulAut S)⁻¹, hl''⟩ : ↥L) = ⟨l, hl⟩ :=
        ι.injective (Subtype.ext h)
      have h3 := congrArg Subtype.val h2
      simp only at h3
      calc (g : MulAut S) * l = (g : MulAut S) * l * (g : MulAut S)⁻¹ * (g : MulAut S) := by
            group
        _ = l * (g : MulAut S) := by rw [h3]
    exact Subtype.ext (hcent g g.2 hcomm)
  have hL : ∀ l : ↥L, e ⟨(l : MulAut S), hLG l.2⟩ = (ι l : Perm (Fin m)) := by
    intro l
    apply hbij.1
    rw [hce]
    ext a
    obtain ⟨y, rfl⟩ := φ.surjective a
    have h1 : (ec ⟨(l : MulAut S), hLG l.2⟩) (φ y) =
        φ (MulAut.conjNormal ⟨(l : MulAut S), hLG l.2⟩ y) := by
      simp [ec, MulAut.congr_apply]
    rw [h1]
    have e1 : MulAut.conjNormal (⟨(l : MulAut S), hLG l.2⟩ : ↥G) y =
        lsOf l * y * (lsOf l)⁻¹ := by
      apply Subtype.ext
      simp [lsOf]
    rw [e1, map_mul, map_mul, map_inv, hφl]
    simp
  exact ⟨e, hinj, fun l _ => hL l⟩

theorem sq_mem_of_embedding {m : ℕ} (hLG : L ≤ G) (ι : ↥L ≃* alternatingGroup (Fin m))
    (e : ↥G →* Perm (Fin m)) (hinj : Function.Injective e)
    (hL : ∀ (l : ↥L) (hl : (l : MulAut S) ∈ G), e ⟨l, hl⟩ = (ι l : Perm (Fin m))) :
    ∀ y ∈ G, y ^ 2 ∈ L := by
  intro y hy
  have hsq : e ⟨y, hy⟩ ^ 2 ∈ alternatingGroup (Fin m) := by
    rw [mem_alternatingGroup, map_pow, Int.units_sq]
  obtain ⟨l, hl⟩ := ι.surjective ⟨_, hsq⟩
  have h1 : e ⟨(l : MulAut S), hLG l.2⟩ = e (⟨y, hy⟩ ^ 2) := by
    rw [hL, hl, map_pow]
  have h2 := congrArg Subtype.val (hinj h1)
  have h3 : (l : MulAut S) = y ^ 2 := by simpa using h2
  rw [← h3]
  exact l.2

theorem ctx_of_b4Hyp [Finite S] (hB : B4Hyp G L) (hT : B42TypeAlt7 ↥L) :
    Bridge.Alt57.Ctx G L 7 := by
  obtain ⟨ι⟩ := nonempty_iso_of_center hT.1 hT.2
  have hF : L = quasithinGenFitting G := hB.2.1
  have hLG : L ≤ G := by rw [hF]; exact CFSG.Quasithin.quasithinGenFitting_le G
  obtain ⟨e, hinj, hL⟩ := exists_embedding_of (by norm_num) (by norm_num) hF hT.1 ι
  exact ⟨Or.inr rfl, ⟨ι⟩, hF, sq_mem_of_embedding hLG ι e hinj hL⟩

theorem card_le_index_pow [Finite S] {m : ℕ} (C : Bridge.Alt57.Ctx G L m)
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤) (A : Subgroup (MulAut S))
    (ι : ↥L ≃* alternatingGroup (Fin m)) (e : ↥G →* Perm (Fin m))
    (hinj : Function.Injective e)
    (hL : ∀ l : ↥L, e ⟨(l : MulAut S), C.le_G l.2⟩ = (ι l : Perm (Fin m))) {r : ℕ}
    (f : Fin r → Perm (Fin m)) (hf : ∀ i, f i ∈ alternatingGroup (Fin m))
    (hcl : alternatingGroup (Fin m) ≤
      Subgroup.closure {x | ∃ i, ∃ b ∈ (A.subgroupOf G).map e, x = f i * b * (f i)⁻¹}) :
    Nat.card S ≤ (fixV A).index ^ r := by
  set A' : Subgroup ↥G := A.subgroupOf G with hA'
  let g : Fin r → ↥G := fun i =>
    ⟨((ι.symm ⟨f i, hf i⟩ : ↥L) : MulAut S), C.le_G (ι.symm ⟨f i, hf i⟩).2⟩
  have hge : ∀ i, e (g i) = f i := fun i => by
    have := hL (ι.symm ⟨f i, hf i⟩)
    rw [ι.apply_symm_apply] at this
    exact this
  let K : Fin r → Subgroup S := fun i =>
    fixV (A.map (MulAut.conj ((g i : ↥G) : MulAut S)).toMonoidHom)
  have hK : ⨅ i, K i = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hvK : ∀ i, v ∈ K i := fun i => (Subgroup.mem_iInf.1 hv) i
    let Stab : Subgroup ↥G :=
      { carrier := {x | ((x : ↥G) : MulAut S) v = v}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          have hx' : ((x : ↥G) : MulAut S) v = v := hx
          have hy' : ((y : ↥G) : MulAut S) v = v := hy
          show ((x * y : ↥G) : MulAut S) v = v
          rw [Subgroup.coe_mul, MulAut.mul_apply, hy', hx']
        inv_mem' := fun {x} hx => by
          have hx' : ((x : ↥G) : MulAut S) v = v := hx
          show (((x⁻¹ : ↥G) : MulAut S)) v = v
          rw [Subgroup.coe_inv]
          have := congrArg (fun w => ((x : ↥G) : MulAut S)⁻¹ w) hx'
          simpa using this.symm }
    let Hg : Subgroup ↥G := Subgroup.closure {x : ↥G | ∃ i, ∃ a ∈ A', x = g i * a * (g i)⁻¹}
    have hHS : Hg ≤ Stab := by
      refine (Subgroup.closure_le Stab).2 ?_
      rintro _ ⟨i, a, ha, rfl⟩
      have hmem : ((g i : ↥G) : MulAut S) * ((a : ↥G) : MulAut S) * ((g i : ↥G) : MulAut S)⁻¹ ∈
          A.map (MulAut.conj ((g i : ↥G) : MulAut S)).toMonoidHom :=
        Subgroup.mem_map.2 ⟨((a : ↥G) : MulAut S), Subgroup.mem_subgroupOf.1 ha, by simp⟩
      have := hvK i _ hmem
      show (((g i * a * (g i)⁻¹ : ↥G) : MulAut S)) v = v
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
    have hAle : alternatingGroup (Fin m) ≤ Hg.map e := by
      refine hcl.trans ?_
      rw [Subgroup.closure_le]
      rintro _ ⟨i, b, hb, rfl⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hb
      rw [← hge i, ← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map.2 ⟨_, Subgroup.subset_closure ⟨i, a, ha, rfl⟩, rfl⟩
    have hvL : v ∈ fixV L := by
      intro l hl
      have hlA : (ι ⟨l, hl⟩ : Perm (Fin m)) ∈ alternatingGroup (Fin m) := (ι ⟨l, hl⟩).2
      obtain ⟨h, hh, hel⟩ := Subgroup.mem_map.1 (hAle hlA)
      have : h = ⟨l, C.le_G hl⟩ := hinj (by rw [hel, hL ⟨l, hl⟩])
      have hS' := hHS hh
      rw [this] at hS'
      exact hS'
    rw [B42A57.fixV_eq_bot_of_irr hirr C.nonab] at hvL
    exact hvL
  have h1 := Subgroup.index_iInf_le K
  rw [hK, Subgroup.index_bot] at h1
  have h2 : ∀ i, (K i).index = (fixV A).index := fun i => B42A57.index_fixV_conj A _
  simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  exact h1

end B42Alt7

end CFSG.Quasithin
