module

public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open

section Geometry

open CFSG.Quasithin

variable {A : Type*} [Group A] {V : Type*} [MulAction A V] {Γ : SimpleGraph V} [GraphAction A Γ]

def burnsideF4f_FixCh (U : Set A) (x l : V) (a : A) : Prop :=
  ∀ u ∈ U, u • (a • x) = a • x ∧ u • (a • l) = a • l

def burnsideF4f_ChRel (U : Set A) (x l : V) (a b : A) : Prop :=
  burnsideF4f_FixCh U x l a ∧ burnsideF4f_FixCh U x l b ∧ (a • x = b • x ∨ a • l = b • l)

theorem burnsideF4f_fixed_geodesic {m : ℕ} (hconn : Γ.Connected) (hU : UniqueGeod Γ m)
    (U : Set A) {u v : V} (hu : ∀ a ∈ U, a • u = u) (hv : ∀ a ∈ U, a • v = v)
    (hlt : Γ.dist u v < m) :
    ∃ p : GPath Γ (Γ.dist u v), p 0 = u ∧ p (Γ.dist u v) = v ∧ ∀ i, ∀ a ∈ U, a • p i = p i := by
  obtain ⟨p, h0, hn, -⟩ := GPath.exists_geodesic hconn u v
  refine ⟨p, h0, hn, fun i a ha => ?_⟩
  have hgeo : p.IsGeodesic := by
    show Γ.dist (p 0) (p (Γ.dist u v)) = Γ.dist u v
    rw [h0, hn]
  have hgeo' : (a • p).IsGeodesic := by
    show Γ.dist ((a • p) 0) ((a • p) (Γ.dist u v)) = Γ.dist u v
    simp only [GPath.smul_apply]
    rw [GPath.dist_smul hconn, h0, hn]
  have hEq := hU _ (a • p) p hgeo' hgeo (by simp [GPath.smul_apply, h0, hu a ha])
    (by simp [GPath.smul_apply, hn, hv a ha]) hlt
  have := congrArg (fun r : GPath Γ (Γ.dist u v) => r i) hEq
  simpa using this

theorem burnsideF4f_walk {typ : V → Bool} (htyp : ∀ a b, Γ.Adj a b → typ a ≠ typ b)
    (htypA : ∀ (g : A) (v : V), typ (g • v) = typ v) {x l : V} (hx : typ x = false)
    (hl : typ l = true)
    (htrans : ∀ a b, Γ.Adj a b → typ a = false → typ b = true →
      ∃ g : A, g • x = a ∧ g • l = b)
    (U : Set A) (p : ℕ → V) (k : ℕ) (hadj : ∀ i, i < k → Γ.Adj (p i) (p (i + 1)))
    (hfix : ∀ i, i ≤ k → ∀ a ∈ U, a • p i = p i) :
    ∀ e : A, burnsideF4f_FixCh U x l e → (e • x = p 0 ∨ e • l = p 0) →
      ∃ e' : A, burnsideF4f_FixCh U x l e' ∧ (e' • x = p k ∨ e' • l = p k) ∧
        Relation.ReflTransGen (burnsideF4f_ChRel U x l) e e' := by
  induction k with
  | zero =>
    intro e he hep
    exact ⟨e, he, hep, Relation.ReflTransGen.refl⟩
  | succ k ih =>
    intro e he hep
    obtain ⟨e', he', hep', hchain⟩ := ih (fun i hi => hadj i (by omega))
      (fun i hi => hfix i (by omega)) e he hep
    have hadjk := hadj k (by omega)
    have hfk := hfix k (by omega)
    have hfk1 := hfix (k + 1) le_rfl
    have hne := htyp _ _ hadjk
    rcases hty : typ (p k) with _ | _
    ·
      have hty1 : typ (p (k + 1)) = true := by
        rcases h : typ (p (k + 1)) with _ | _
        · exact absurd (hty.trans h.symm) hne
        · rfl
      obtain ⟨g, hgx, hgl⟩ := htrans (p k) (p (k + 1)) hadjk hty hty1
      have hgfix : burnsideF4f_FixCh U x l g := fun u hu =>
        ⟨by rw [hgx]; exact hfk u hu, by rw [hgl]; exact hfk1 u hu⟩
      have he'x : e' • x = p k := by
        rcases hep' with h | h
        · exact h
        · exfalso
          have := htypA e' l
          rw [h, hl, hty] at this
          exact absurd this (by decide)
      refine ⟨g, hgfix, Or.inr hgl, hchain.tail ⟨he', hgfix, Or.inl (he'x.trans hgx.symm)⟩⟩
    ·
      have hty0 : typ (p (k + 1)) = false := by
        rcases h : typ (p (k + 1)) with _ | _
        · rfl
        · exact absurd (hty.trans h.symm) hne
      obtain ⟨g, hgx, hgl⟩ := htrans (p (k + 1)) (p k) hadjk.symm hty0 hty
      have hgfix : burnsideF4f_FixCh U x l g := fun u hu =>
        ⟨by rw [hgx]; exact hfk1 u hu, by rw [hgl]; exact hfk u hu⟩
      have he'l : e' • l = p k := by
        rcases hep' with h | h
        · exfalso
          have := htypA e' x
          rw [h, hx, hty] at this
          exact absurd this (by decide)
        · exact h
      refine ⟨g, hgfix, Or.inl hgx, hchain.tail ⟨he', hgfix, Or.inr (he'l.trans hgl.symm)⟩⟩

theorem burnsideF4f_chain {m : ℕ} (hconn : Γ.Connected) (hdiam : ∀ u v, Γ.dist u v ≤ m)
    (hU : UniqueGeod Γ m) {typ : V → Bool} (htyp : ∀ a b, Γ.Adj a b → typ a ≠ typ b)
    (htypA : ∀ (g : A) (v : V), typ (g • v) = typ v) {x l : V} (hxl : Γ.Adj x l)
    (hx : typ x = false) (hl : typ l = true)
    (htrans : ∀ a b, Γ.Adj a b → typ a = false → typ b = true →
      ∃ g : A, g • x = a ∧ g • l = b)
    (U : Set A) (hUx : ∀ u ∈ U, u • x = x) (hUl : ∀ u ∈ U, u • l = l) (g : A)
    (hgx : ∀ u ∈ U, (g * u * g⁻¹) • x = x) (hgl : ∀ u ∈ U, (g * u * g⁻¹) • l = l) :
    Relation.ReflTransGen (burnsideF4f_ChRel U x l) 1 g⁻¹ := by
  have hx' : ∀ u ∈ U, u • (g⁻¹ • x) = g⁻¹ • x := by
    intro u hu
    have h := hgx u hu
    calc u • (g⁻¹ • x) = (g⁻¹ * (g * u * g⁻¹)) • x := by
          rw [mul_smul]; simp [mul_smul, mul_assoc]
      _ = g⁻¹ • x := by rw [mul_smul, h]
  have hl' : ∀ u ∈ U, u • (g⁻¹ • l) = g⁻¹ • l := by
    intro u hu
    have h := hgl u hu
    calc u • (g⁻¹ • l) = (g⁻¹ * (g * u * g⁻¹)) • l := by
          rw [mul_smul]; simp [mul_smul, mul_assoc]
      _ = g⁻¹ • l := by rw [mul_smul, h]
  have hFg : burnsideF4f_FixCh U x l g⁻¹ := fun u hu => ⟨hx' u hu, hl' u hu⟩
  have hF1 : burnsideF4f_FixCh U x l (1 : A) := fun u hu => by simpa using And.intro (hUx u hu) (hUl u hu)
  have hxx' : typ (g⁻¹ • x) = false := by rw [htypA, hx]
  have hsucc := GPath.dist_adj_succ_or hconn htyp (g⁻¹ • x) hxl
  have hdx := hdiam (g⁻¹ • x) x
  have hdl := hdiam (g⁻¹ • x) l
  have key : ∀ v : V, (1 : A) • x = v ∨ (1 : A) • l = v → (∀ u ∈ U, u • v = v) →
      Γ.dist v (g⁻¹ • x) < m → Relation.ReflTransGen (burnsideF4f_ChRel U x l) 1 g⁻¹ := by
    intro v hv hvfix hlt
    obtain ⟨p, hp0, hpn, hpfix⟩ := burnsideF4f_fixed_geodesic hconn hU U hvfix (hx' ) hlt
    obtain ⟨e', he', hep', hchain⟩ := burnsideF4f_walk htyp htypA hx hl htrans U p.toFun
      (Γ.dist v (g⁻¹ • x)) (fun i hi => p.adj i hi) (fun i _ a ha => hpfix i a ha) 1 hF1
      (by simpa [hp0] using hv)
    have hpn' : p.toFun (Γ.dist v (g⁻¹ • x)) = g⁻¹ • x := hpn
    rw [hpn'] at hep'
    have he'x : e' • x = g⁻¹ • x := by
      rcases hep' with h | h
      · exact h
      · exfalso
        have := htypA e' l
        rw [h, hl, hxx'] at this
        exact absurd this (by decide)
    exact hchain.tail ⟨he', hFg, Or.inl he'x⟩
  rcases hsucc with h | h
  ·
    refine key x (Or.inl (one_smul _ _)) hUx ?_
    rw [SimpleGraph.dist_comm]
    omega
  · refine key l (Or.inr (one_smul _ _)) hUl ?_
    rw [SimpleGraph.dist_comm]
    omega

end Geometry

section Incl

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

noncomputable def burnsideF4f_toG0 (hgen : M₁ ⊔ M₂ = ⊤) : E →* (incl M₁ M₂).G0 where
  toFun g := ⟨⟨g, by rw [hgen]; exact Subgroup.mem_top g⟩, by
    rw [(incl M₁ M₂).gen]; exact Subgroup.mem_top _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem burnsideF4f_toG0_surj (hgen : M₁ ⊔ M₂ = ⊤) (k : (incl M₁ M₂).G0) :
    ∃ g : E, burnsideF4f_toG0 hgen g = k :=
  ⟨((k : ↥(M₁ ⊔ M₂)) : E), Subtype.ext (Subtype.ext rfl)⟩

theorem burnsideF4f_smul_xv_iff (hgen : M₁ ⊔ M₂ = ⊤) (g : E) :
    burnsideF4f_toG0 hgen g • (incl M₁ M₂).xv = (incl M₁ M₂).xv ↔ g ∈ M₁ := by
  constructor
  · intro h
    have h1 := CosetGeom.mem_stab_of_smul_eq h
    rw [CosetGeom.stab_γ₀ (G₀ := (incl M₁ M₂).φ1.range ⊔ (incl M₁ M₂).φ2.range) le_sup_left] at h1
    obtain ⟨a, ha⟩ := h1
    have := congrArg (fun z : ↥(M₁ ⊔ M₂) => (z : E)) ha
    simp only [burnsideF4f_toG0] at this
    have h2 : ((show ↥M₁ from a) : E) = g := this
    exact h2 ▸ (show ↥M₁ from a).2
  · intro hg
    apply CosetGeom.smul_eq_of_mem_stab
    rw [CosetGeom.stab_γ₀ (G₀ := (incl M₁ M₂).φ1.range ⊔ (incl M₁ M₂).φ2.range) le_sup_left]
    exact ⟨⟨g, hg⟩, rfl⟩

theorem burnsideF4f_smul_lv_iff (hgen : M₁ ⊔ M₂ = ⊤) (g : E) :
    burnsideF4f_toG0 hgen g • (incl M₁ M₂).lv = (incl M₁ M₂).lv ↔ g ∈ M₂ := by
  constructor
  · intro h
    have h1 := CosetGeom.mem_stab_of_smul_eq h
    rw [CosetGeom.stab_γ₁ (G₀ := (incl M₁ M₂).φ1.range ⊔ (incl M₁ M₂).φ2.range) le_sup_right] at h1
    obtain ⟨a, ha⟩ := h1
    have := congrArg (fun z : ↥(M₁ ⊔ M₂) => (z : E)) ha
    simp only [burnsideF4f_toG0] at this
    have h2 : ((show ↥M₂ from a) : E) = g := this
    exact h2 ▸ (show ↥M₂ from a).2
  · intro hg
    apply CosetGeom.smul_eq_of_mem_stab
    rw [CosetGeom.stab_γ₁ (G₀ := (incl M₁ M₂).φ1.range ⊔ (incl M₁ M₂).φ2.range) le_sup_right]
    exact ⟨⟨g, hg⟩, rfl⟩

def burnsideF4f_ChRelE (M₁ M₂ : Subgroup E) (U : Set E) (a b : E) : Prop :=
  (∀ u ∈ U, a⁻¹ * u * a ∈ M₁ ⊓ M₂) ∧ (∀ u ∈ U, b⁻¹ * u * b ∈ M₁ ⊓ M₂) ∧
    (a⁻¹ * b ∈ M₁ ∨ a⁻¹ * b ∈ M₂)

theorem burnsideF4f_chain_E (hgen : M₁ ⊔ M₂ = ⊤) {m : ℕ}
    (hpoly : IsGenPolygon (incl M₁ M₂).graph m) (U : Set E) (hU : ∀ u ∈ U, u ∈ M₁ ⊓ M₂) (g : E)
    (hg : ∀ u ∈ U, g * u * g⁻¹ ∈ M₁ ⊓ M₂) :
    Relation.ReflTransGen (burnsideF4f_ChRelE M₁ M₂ U) 1 g⁻¹ := by
  letI : MulAction E (incl M₁ M₂).Γ := MulAction.compHom _ (burnsideF4f_toG0 hgen)
  haveI : GraphAction E (incl M₁ M₂).graph :=
    ⟨fun g a b => CosetGeom.smul_adj (burnsideF4f_toG0 hgen g)⟩
  have hxM : ∀ g : E, g • (incl M₁ M₂).xv = (incl M₁ M₂).xv ↔ g ∈ M₁ :=
    fun g => burnsideF4f_smul_xv_iff hgen g
  have hlM : ∀ g : E, g • (incl M₁ M₂).lv = (incl M₁ M₂).lv ↔ g ∈ M₂ :=
    fun g => burnsideF4f_smul_lv_iff hgen g
  have htrans : ∀ a b : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.Adj a b → CosetGeom.vtype a = false →
      CosetGeom.vtype b = true →
      ∃ g : E, g • (incl M₁ M₂).xv = a ∧ g • (incl M₁ M₂).lv = b := by
    intro a b hab ha hb
    rcases a with p | p <;> rcases b with q | q
    · exact absurd hb (by simp [CosetGeom.vtype])
    · obtain ⟨k, hk1, hk2⟩ := CosetGeom.adj_inl_inr.mp hab
      obtain ⟨g, hg⟩ := burnsideF4f_toG0_surj hgen k
      refine ⟨g, ?_, ?_⟩
      · show burnsideF4f_toG0 hgen g • (incl M₁ M₂).xv = _
        rw [hg, CosetGeom.smul_γ₀, hk1]
      · show burnsideF4f_toG0 hgen g • (incl M₁ M₂).lv = _
        rw [hg, CosetGeom.smul_γ₁, hk2]
    · exact absurd ha (by simp [CosetGeom.vtype])
    · exact absurd ha (by simp [CosetGeom.vtype])
  have hch := burnsideF4f_chain (A := E) (Γ := (incl M₁ M₂).graph) (m := m) hpoly.connected
    hpoly.diam_le hpoly.uniqueGeod (typ := CosetGeom.vtype)
    (fun a b h => CosetGeom.vtype_ne_of_adj h)
    (fun g v => CosetGeom.vtype_smul (burnsideF4f_toG0 hgen g) v)
    (x := (incl M₁ M₂).xv) (l := (incl M₁ M₂).lv) CosetGeom.adj_γ₀_γ₁ rfl rfl htrans U
    (fun u hu => (hxM u).mpr (hU u hu).1) (fun u hu => (hlM u).mpr (hU u hu).2) g
    (fun u hu => (hxM _).mpr (hg u hu).1) (fun u hu => (hlM _).mpr (hg u hu).2)
  have hfix : ∀ a : E, burnsideF4f_FixCh U (incl M₁ M₂).xv (incl M₁ M₂).lv a →
      ∀ u ∈ U, a⁻¹ * u * a ∈ M₁ ⊓ M₂ := by
    intro a ha u hu
    obtain ⟨h1, h2⟩ := ha u hu
    refine ⟨(hxM _).mp ?_, (hlM _).mp ?_⟩
    · calc (a⁻¹ * u * a) • (incl M₁ M₂).xv = a⁻¹ • (u • (a • (incl M₁ M₂).xv)) := by
            rw [mul_smul, mul_smul]
        _ = (incl M₁ M₂).xv := by rw [h1, inv_smul_smul]
    · calc (a⁻¹ * u * a) • (incl M₁ M₂).lv = a⁻¹ • (u • (a • (incl M₁ M₂).lv)) := by
            rw [mul_smul, mul_smul]
        _ = (incl M₁ M₂).lv := by rw [h2, inv_smul_smul]
  refine Relation.ReflTransGen.mono (p := burnsideF4f_ChRelE M₁ M₂ U) ?_ _ _ hch
  intro a b hab
  refine ⟨hfix a hab.1, hfix b hab.2.1, ?_⟩
  rcases hab.2.2 with h | h
  · left
    refine (hxM _).mp ?_
    calc (a⁻¹ * b) • (incl M₁ M₂).xv = a⁻¹ • (b • (incl M₁ M₂).xv) := mul_smul _ _ _
      _ = (incl M₁ M₂).xv := by rw [← h, inv_smul_smul]
  · right
    refine (hlM _).mp ?_
    calc (a⁻¹ * b) • (incl M₁ M₂).lv = a⁻¹ • (b • (incl M₁ M₂).lv) := mul_smul _ _ _
      _ = (incl M₁ M₂).lv := by rw [← h, inv_smul_smul]

end Incl

section Transfer

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]

open scoped Classical in
noncomputable def burnsideF4f_bm (β : Cpl M₁ M₂ Y) (x : E) : β.G0 :=
  if h : x ∈ M₁ ⊓ M₂ then bmap β ⟨x, h⟩ else 1

theorem burnsideF4f_bm_of_mem (β : Cpl M₁ M₂ Y) (u : ↥(M₁ ⊓ M₂)) :
    burnsideF4f_bm β (u : E) = bmap β u := by
  unfold burnsideF4f_bm
  rw [dif_pos u.2]

theorem burnsideF4f_f2_eq_f1 (β : Cpl M₁ M₂ Y) (u : ↥(M₁ ⊓ M₂)) :
    f2 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α2 u) =
      f1 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 u) := by
  apply Subtype.ext
  exact (β.comm2 u).trans (β.comm1 u).symm

theorem burnsideF4f_hom_conj {H K : Type*} [Group H] [Group K] (φ : H →* K) (m w : H) :
    φ (m⁻¹ * w * m) = (φ m)⁻¹ * φ w * φ m := by simp

theorem burnsideF4f_bm_conj₁ (β : Cpl M₁ M₂ Y) {m w : E} (hm : m ∈ M₁) (hw : w ∈ M₁ ⊓ M₂)
    (hw' : m⁻¹ * w * m ∈ M₁ ⊓ M₂) :
    burnsideF4f_bm β (m⁻¹ * w * m) =
      (f1 (c := β) ⟨m, hm⟩)⁻¹ * burnsideF4f_bm β w * f1 (c := β) ⟨m, hm⟩ := by
  unfold burnsideF4f_bm
  rw [dif_pos hw, dif_pos hw']
  exact burnsideF4f_hom_conj (f1 (c := β)) ⟨m, hm⟩ ⟨w, hw.1⟩

theorem burnsideF4f_bm_conj₂ (β : Cpl M₁ M₂ Y) {m w : E} (hm : m ∈ M₂) (hw : w ∈ M₁ ⊓ M₂)
    (hw' : m⁻¹ * w * m ∈ M₁ ⊓ M₂) :
    burnsideF4f_bm β (m⁻¹ * w * m) =
      (f2 (c := β) ⟨m, hm⟩)⁻¹ * burnsideF4f_bm β w * f2 (c := β) ⟨m, hm⟩ := by
  unfold burnsideF4f_bm
  rw [dif_pos hw, dif_pos hw']
  show bmap β ⟨m⁻¹ * w * m, hw'⟩ = _
  have e1 : ∀ (z : ↥(M₁ ⊓ M₂)), bmap β z = f2 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α2 z) :=
    fun z => (burnsideF4f_f2_eq_f1 β z).symm
  rw [e1, e1]
  exact burnsideF4f_hom_conj (f2 (c := β)) ⟨m, hm⟩ ⟨w, hw.2⟩

theorem burnsideF4f_transfer (β : Cpl M₁ M₂ Y) (Ū : Set E) {c : E}
    (hchain : Relation.ReflTransGen (burnsideF4f_ChRelE M₁ M₂ Ū) 1 c) :
    ∃ h : β.G0, ∀ u ∈ Ū, burnsideF4f_bm β (c⁻¹ * u * c) = h⁻¹ * burnsideF4f_bm β u * h := by
  induction hchain with
  | refl => exact ⟨1, fun u _ => by simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨h, hh⟩ := ih
    obtain ⟨hFb, hFc, hbc'⟩ := hbc
    have hconj : ∀ u : E, c⁻¹ * u * c = (b⁻¹ * c)⁻¹ * (b⁻¹ * u * b) * (b⁻¹ * c) := by
      intro u; group
    rcases hbc' with hm | hm
    · refine ⟨h * f1 (c := β) ⟨b⁻¹ * c, hm⟩, fun u hu => ?_⟩
      rw [hconj, burnsideF4f_bm_conj₁ β hm (hFb u hu) (by rw [← hconj]; exact hFc u hu), hh u hu]
      group
    · refine ⟨h * f2 (c := β) ⟨b⁻¹ * c, hm⟩, fun u hu => ?_⟩
      rw [hconj, burnsideF4f_bm_conj₂ β hm (hFb u hu) (by rw [← hconj]; exact hFc u hu), hh u hu]
      group

theorem burnsideF4f_F430_core (hgen : M₁ ⊔ M₂ = ⊤) {m : ℕ}
    (hpoly : IsGenPolygon (incl M₁ M₂).graph m) (β : Cpl M₁ M₂ Y)
    (U U' : Set ↥(M₁ ⊓ M₂)) (g : E)
    (hg : (fun u : E => g * u * g⁻¹) '' (Subtype.val '' U) = Subtype.val '' U') :
    ∃ h : β.G0, (fun w : β.G0 => h * w * h⁻¹) '' (bmap β '' U) = bmap β '' U' := by
  have hU : ∀ u ∈ (Subtype.val '' U : Set E), u ∈ M₁ ⊓ M₂ := by
    rintro _ ⟨u, -, rfl⟩; exact u.2
  have hgU : ∀ u ∈ (Subtype.val '' U : Set E), g * u * g⁻¹ ∈ M₁ ⊓ M₂ := by
    intro u hu
    have : g * u * g⁻¹ ∈ Subtype.val '' U' := hg ▸ ⟨u, hu, rfl⟩
    obtain ⟨u', -, hu'⟩ := this
    exact hu' ▸ u'.2
  have hch := burnsideF4f_chain_E hgen hpoly (Subtype.val '' U) hU g hgU
  obtain ⟨h, hh⟩ := burnsideF4f_transfer β _ hch
  have hh' : ∀ u ∈ (Subtype.val '' U : Set E),
      burnsideF4f_bm β (g * u * g⁻¹) = h⁻¹ * burnsideF4f_bm β u * h := by
    intro u hu
    simpa only [inv_inv] using hh u hu
  refine ⟨h⁻¹, ?_⟩
  ext z
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    have hmem : g * (u : E) * g⁻¹ ∈ Subtype.val '' U' := hg ▸ ⟨u, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨u', hu', hu'e⟩ := hmem
    refine ⟨u', hu', ?_⟩
    have h1 := hh' (u : E) ⟨u, hu, rfl⟩
    rw [← hu'e, burnsideF4f_bm_of_mem, burnsideF4f_bm_of_mem] at h1
    show bmap β u' = h⁻¹ * bmap β u * h⁻¹⁻¹
    rw [h1, inv_inv]
  · rintro ⟨u', hu', rfl⟩
    have hmem : (u' : E) ∈ (fun u : E => g * u * g⁻¹) '' (Subtype.val '' U) :=
      hg ▸ ⟨u', hu', rfl⟩
    obtain ⟨_, ⟨u, hu, rfl⟩, hue⟩ := hmem
    refine ⟨bmap β u, ⟨u, hu, rfl⟩, ?_⟩
    have h1 := hh' (u : E) ⟨u, hu, rfl⟩
    have hue' : g * (u : E) * g⁻¹ = (u' : E) := hue
    rw [hue', burnsideF4f_bm_of_mem, burnsideF4f_bm_of_mem] at h1
    show h⁻¹ * bmap β u * h⁻¹⁻¹ = bmap β u'
    rw [h1, inv_inv]

end Transfer

section Assembly

open CFSG.Quasithin CFSG.ASVolI.ChF

def burnsideF4f_PolygonTwo : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ 2 f Gp M₁ M₂ → IsGenPolygon (incl M₁ M₂).graph κ.m

theorem burnsideF4f_polygonTwo_of_F45 (h : F_4_5) : burnsideF4f_PolygonTwo :=
  fun κ f E _ Gp M₁ M₂ hyp => (h κ 2 f E Gp M₁ M₂ hyp (incl M₁ M₂) rfl).1

theorem burnsideF4f_F430_of_polygon (hpoly : burnsideF4f_PolygonTwo) : F_4_30 := by
  intro κ f E _ Gp M₁ M₂ hyp T hT Y _ β hβ U U' hUT hU'T hconj
  obtain ⟨g, hg⟩ := hconj
  exact burnsideF4f_F430_core hyp.toHypF_4_4g.gen (hpoly κ f E Gp M₁ M₂ hyp) β U U' g hg

theorem burnsideF4f_F430_of_F45 (h : F_4_5) : F_4_30 :=
  burnsideF4f_F430_of_polygon (burnsideF4f_polygonTwo_of_F45 h)

def burnsideF4f_PolygonKind (κ : GLKind) : Prop :=
  ∀ (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ 2 f Gp M₁ M₂ → IsGenPolygon (incl M₁ M₂).graph κ.m

def burnsideF4f_F430_kind (κ : GLKind) : Prop :=
  ∀ (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ 2 f Gp M₁ M₂ →
    ∀ T : Subgroup E, IsSylowOf 2 T (M₁ ⊓ M₂) →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
    ∀ U U' : Set ↥(M₁ ⊓ M₂), (∀ u ∈ U, (u : E) ∈ T) → (∀ u ∈ U', (u : E) ∈ T) →
      (∃ g : E, (fun u : E => g * u * g⁻¹) '' (Subtype.val '' U) = Subtype.val '' U') →
      ∃ h : β.G0, (fun w : β.G0 => h * w * h⁻¹) '' (bmap β '' U) = bmap β '' U'

theorem burnsideF4f_polygonTwo_of_kinds (h : ∀ κ, burnsideF4f_PolygonKind κ) :
    burnsideF4f_PolygonTwo := fun κ => h κ

theorem burnsideF4f_F430_of_kinds (h : ∀ κ, burnsideF4f_F430_kind κ) : F_4_30 := fun κ => h κ

theorem burnsideF4f_F430_kind_of_polygon {κ : GLKind} (hpoly : burnsideF4f_PolygonKind κ) :
    burnsideF4f_F430_kind κ := by
  intro f E _ Gp M₁ M₂ hyp T hT Y _ β hβ U U' hUT hU'T hconj
  obtain ⟨g, hg⟩ := hconj
  exact burnsideF4f_F430_core hyp.toHypF_4_4g.gen (hpoly f E Gp M₁ M₂ hyp) β U U' g hg

end Assembly

section F427

open CFSG.ASVolI.ChF

def burnsideF4f_F427partial_kind (κ : GLKind) : Prop :=
  ∀ (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ 2 f Gp M₁ M₂ → Gp = ⊤ →
    ((κ = .L3 ∨ κ = .G2d) → Set.ncard (InvClasses E) = 1) ∧
    (κ = .Sp4 → Set.ncard (InvClasses E) = 3 ∧
      ∀ C ∈ InvClasses E, ClassMeetsCenter (pCoreOf 2 (M₁ ⊓ M₂)) C) ∧
    ((κ ≠ .L3 ∧ κ ≠ .Sp4 ∧ κ ≠ .G2d) → Set.ncard (InvClasses E) = 2 ∧
      ∃! C : ConjClasses E, C ∈ InvClasses E ∧ ClassMeetsCenter (pCoreOf 2 (M₁ ⊓ M₂)) C) ∧
    (κ ≠ .L3 →
      (∀ z ∈ ctr (oPPrime 2 M₁), z ≠ 1 →
        (κ ≠ .G2d → z * z = 1) ∧ Subgroup.centralizer ({z} : Set E) ≤ M₁ ∧
          oPPrime 2 M₁ = oPPrime 2 (Subgroup.centralizer ({z} : Set E)) ∧
          ((κ ≠ .U4 ∧ κ ≠ .U5) → oPPrime 2 M₁ = Subgroup.centralizer ({z} : Set E))) ∧
      (κ ≠ .G2d → ∃ t ∈ pCoreOf 2 M₂, IsShortRootInv κ Gp M₁ M₂ t ∧
        Subgroup.centralizer ({t} : Set E) ≤ M₂)) ∧
    (κ = .L3 → ∀ z ∈ ctr (pCoreOf 2 (M₁ ⊓ M₂)), z ≠ 1 →
      pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Subgroup.centralizer ({z} : Set E)))

def burnsideF4f_F427_kind (κ : GLKind) : Prop :=
  ∀ (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E)
    (hyp : HypF_4_4 κ 2 f Gp M₁ M₂), Gp = ⊤ →
    let chart := hyp.toHypF_4_4g.chart
    chart.Matches M₁ M₂ ∧
    ((κ = .L3 ∨ κ = .G2d) → Set.ncard (InvClasses E) = 1 ∧
      ∀ element : E, element ≠ 1 → element * element = 1 →
        chart.RootInvolution false element) ∧
    (∀ kind : κ = .Sp4, Set.ncard (InvClasses E) = 3 ∧
      (∀ C ∈ InvClasses E, ClassMeetsCenter (pCoreOf 2 (M₁ ⊓ M₂)) C) ∧
      ∃ long short mixed : E,
        chart.RootInvolution false long ∧ chart.RootInvolution true short ∧
        mixed ∈ Gp ∧ mixed ≠ 1 ∧ mixed * mixed = 1 ∧
        (∃ conjugator ∈ Gp, ∃ a ∈ chart.longRoot, ∃ b ∈ chart.shortRoot,
          a ≠ 1 ∧ b ≠ 1 ∧ conjugator * mixed * conjugator⁻¹ = a * b) ∧
        ¬ IsConj long short ∧ ¬ IsConj long mixed ∧ ¬ IsConj short mixed ∧
        (∀ element : E, element ≠ 1 → element * element = 1 →
          IsConj element long ∨ IsConj element short ∨ IsConj element mixed) ∧
        (∀ element : E, chart.RootInvolution false element ↔ IsConj element long) ∧
        (∀ element : E, chart.RootInvolution true element ↔ IsConj element short) ∧
        (∀ element : E, (kind ▸ chart).C2Involution element ↔ IsConj element mixed)) ∧
    ((κ ≠ .L3 ∧ κ ≠ .Sp4 ∧ κ ≠ .G2d) →
      Set.ncard (InvClasses E) = 2 ∧
      (∃! C : ConjClasses E, C ∈ InvClasses E ∧
        ClassMeetsCenter (pCoreOf 2 (M₁ ⊓ M₂)) C) ∧
      (∀ element : E, element ≠ 1 → element * element = 1 →
        chart.RootInvolution false element ∨ chart.RootInvolution true element) ∧
      (∀ element : E, element ≠ 1 → element * element = 1 →
        (chart.RootInvolution false element ↔
          ∃ conjugator ∈ Gp, conjugator * element * conjugator⁻¹ ∈
            ctr (pCoreOf 2 (M₁ ⊓ M₂)))) ∧
      (∀ element : E, ¬ (chart.RootInvolution false element ∧
        chart.RootInvolution true element))) ∧
    (κ ≠ .L3 →
      (∀ element ∈ ctr (oPPrime 2 M₁), element ≠ 1 →
        (κ ≠ .G2d → chart.RootInvolution false element) ∧
        (κ = .G2d → element * element = 1 → chart.RootInvolution false element) ∧
        Subgroup.centralizer ({element} : Set E) ≤ M₁ ∧
        oPPrime 2 M₁ = oPPrime 2 (Subgroup.centralizer ({element} : Set E)) ∧
        ((κ ≠ .U4 ∧ κ ≠ .U5) →
          oPPrime 2 M₁ = Subgroup.centralizer ({element} : Set E))) ∧
      (κ ≠ .G2d → ∃ element ∈ pCoreOf 2 M₂,
        chart.RootInvolution true element ∧
        Subgroup.centralizer ({element} : Set E) ≤ M₂)) ∧
    (κ = .L3 → ∀ element ∈ ctr (pCoreOf 2 (M₁ ⊓ M₂)), element ≠ 1 →
      pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Subgroup.centralizer ({element} : Set E)))

theorem burnsideF4f_F427partial_of_kinds (h : ∀ κ, burnsideF4f_F427partial_kind κ) :
    F_4_27_partial := fun κ => h κ

theorem burnsideF4f_F427_of_kinds (h : ∀ κ, burnsideF4f_F427_kind κ) : F_4_27 := fun κ => h κ

theorem burnsideF4f_F427partial_kind_of_kind {κ : GLKind} (h : burnsideF4f_F427_kind κ) :
    burnsideF4f_F427partial_kind κ := by
  intro f E _ Gp M₁ M₂ hyp hGp
  obtain ⟨hM, h1, h2, h3, h4, h5⟩ := h f E Gp M₁ M₂ hyp hGp
  refine ⟨fun hk => (h1 hk).1, ?_, ?_, ?_, h5⟩
  · intro hk
    obtain ⟨hn, hc, -⟩ := h2 hk
    exact ⟨hn, hc⟩
  · intro hk
    obtain ⟨hn, hu, -⟩ := h3 hk
    exact ⟨hn, hu⟩
  · intro hk
    obtain ⟨ha, hb⟩ := h4 hk
    refine ⟨fun z hz hz1 => ?_, fun hG => ?_⟩
    · obtain ⟨c1, c2, c3, c4, c5⟩ := ha z hz hz1
      exact ⟨fun hG => (c1 hG).2.2.1, c3, c4, c5⟩
    · obtain ⟨t, ht, hrt, hct⟩ := hb hG
      exact ⟨t, ht, ⟨f, hyp.toHypF_4_4g.chart, hM, hrt⟩, hct⟩

theorem burnsideF4f_F427partial_of_F427 (h : F_4_27) : F_4_27_partial :=
  burnsideF4f_F427partial_of_kinds fun κ => burnsideF4f_F427partial_kind_of_kind
    fun f E _ Gp M₁ M₂ hyp hGp => h κ f E Gp M₁ M₂ hyp hGp

end F427

section L3

open CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots

theorem burnsideF4f_mem_rawStabilizer {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (space : Set (ι → K)) (g : GL ι K) :
    g ∈ rawStabilizer space ↔ ∀ v, (g : Matrix ι ι K).mulVec v ∈ space ↔ v ∈ space := by
  let T : Subgroup (GL ι K) :=
    { carrier := {actor | ∀ v, (actor : Matrix ι ι K).mulVec v ∈ space ↔ v ∈ space}
      one_mem' := by intro v; simp
      mul_mem' := by
        intro a b ha hb v
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
      inv_mem' := by
        intro a ha v
        have h1 := ha (((a⁻¹ : GL ι K) : Matrix ι ι K).mulVec v)
        have h2 : (a : Matrix ι ι K).mulVec (((a⁻¹ : GL ι K) : Matrix ι ι K).mulVec v) = v := by
          rw [Matrix.mulVec_mulVec]; simp
        rw [h2] at h1
        exact h1.symm }
  have hT : Subgroup.closure ({actor | ∀ v, (actor : Matrix ι ι K).mulVec v ∈ space ↔ v ∈ space} :
      Set (GL ι K)) = T := Subgroup.closure_eq T
  unfold rawStabilizer
  rw [hT]
  exact Iff.rfl

theorem burnsideF4f_L3_marking {prime degree : ℕ} {E : Type} [Group E] {core : Subgroup E}
    (chart : NativeChart .L3 prime degree core) :
    ∃ marking : Marking .L3 prime degree core,
      chart.borel = marking.borel.map core.subtype ∧
      chart.points = (marking.parabolic false).map core.subtype ∧
      chart.lines = (marking.parabolic true).map core.subtype ∧
      chart.longRoot = (marking.root .a13 false).map core.subtype := by
  rcases chart.coordinates with ⟨c, hk, marking, h1, h2, h3, h4, h5⟩ | ⟨hk, _⟩ | ⟨hk, _⟩ |
    ⟨hk, _⟩ | ⟨_, _, _, _, _, _, _, ⟨hk, _⟩ | ⟨hk, _⟩⟩
  · cases c
    · exact ⟨marking, h1, h2, h3, by simpa using h4⟩
    all_goals exact absurd hk (by simp [classicalKind])
  all_goals exact absurd hk (by simp)

section L3Entries

variable {K : Type} [Field K]

theorem burnsideF4f_mem_coordinateSpace_one (v : Fin 3 → K) :
    v ∈ coordinateSpace (K := K) (flagOne .L3) ↔ v 1 = 0 ∧ v 2 = 0 := by
  simp only [coordinateSpace, flagOne, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨h 1 (by decide), h 2 (by decide)⟩
  · rintro ⟨h1, h2⟩ i hi
    fin_cases i
    · exact absurd rfl hi
    · exact h1
    · exact h2

theorem burnsideF4f_mem_coordinateSpace_two (v : Fin 3 → K) :
    v ∈ coordinateSpace (K := K) (flagTwo .L3) ↔ v 2 = 0 := by
  simp only [coordinateSpace, flagTwo, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro h
    exact h 2 (by decide)
  · intro h2 i hi
    fin_cases i
    · exact absurd (Or.inl rfl) hi
    · exact absurd (Or.inr rfl) hi
    · exact h2

theorem burnsideF4f_det_of_col {g : Matrix (Fin 3) (Fin 3) K} (h10 : g 1 0 = 0) (h20 : g 2 0 = 0) :
    g.det = g 0 0 * (g 1 1 * g 2 2 - g 1 2 * g 2 1) := by
  rw [Matrix.det_fin_three, h10, h20]
  ring

theorem burnsideF4f_stab_one (g : GL (Fin 3) K) :
    g ∈ rawStabilizer ((fun v => ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v) ''
      coordinateSpace (K := K) (flagOne .L3)) ↔ g.val 1 0 = 0 ∧ g.val 2 0 = 0 := by
  rw [burnsideF4f_mem_rawStabilizer]
  simp only [Units.val_one, Matrix.one_mulVec, Set.image_id']
  constructor
  · intro h
    have h1 := (h (Pi.single 0 1)).mpr (by
      rw [burnsideF4f_mem_coordinateSpace_one]; simp)
    rw [burnsideF4f_mem_coordinateSpace_one] at h1
    simpa [Matrix.mulVec_single_one] using h1
  · rintro ⟨h10, h20⟩ v
    rw [burnsideF4f_mem_coordinateSpace_one, burnsideF4f_mem_coordinateSpace_one]
    have hdet : g.val.det ≠ 0 := by
      have := g.isUnit
      exact (Matrix.isUnit_iff_isUnit_det _).mp this |>.ne_zero
    rw [burnsideF4f_det_of_col h10 h20] at hdet
    have hΔ : g.val 1 1 * g.val 2 2 - g.val 1 2 * g.val 2 1 ≠ 0 := fun h => hdet (by rw [h]; ring)
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20]
    constructor
    · rintro ⟨e1, e2⟩
      have a1 : g.val 1 1 * v 1 + g.val 1 2 * v 2 = 0 := by linear_combination e1
      have a2 : g.val 2 1 * v 1 + g.val 2 2 * v 2 = 0 := by linear_combination e2
      constructor
      · have : (g.val 1 1 * g.val 2 2 - g.val 1 2 * g.val 2 1) * v 1 = 0 := by
          linear_combination g.val 2 2 * a1 - g.val 1 2 * a2
        exact (mul_eq_zero.mp this).resolve_left hΔ
      · have : (g.val 1 1 * g.val 2 2 - g.val 1 2 * g.val 2 1) * v 2 = 0 := by
          linear_combination g.val 1 1 * a2 - g.val 2 1 * a1
        exact (mul_eq_zero.mp this).resolve_left hΔ
    · rintro ⟨e1, e2⟩
      simp [e1, e2]

theorem burnsideF4f_stab_two (g : GL (Fin 3) K) :
    g ∈ rawStabilizer ((fun v => ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v) ''
      coordinateSpace (K := K) (flagTwo .L3)) ↔ g.val 2 0 = 0 ∧ g.val 2 1 = 0 := by
  rw [burnsideF4f_mem_rawStabilizer]
  simp only [Units.val_one, Matrix.one_mulVec, Set.image_id']
  constructor
  · intro h
    have h0 := (h (Pi.single 0 1)).mpr (by
      rw [burnsideF4f_mem_coordinateSpace_two]; simp)
    have h1 := (h (Pi.single 1 1)).mpr (by
      rw [burnsideF4f_mem_coordinateSpace_two]; simp)
    rw [burnsideF4f_mem_coordinateSpace_two] at h0 h1
    exact ⟨by simpa [Matrix.mulVec_single_one] using h0,
      by simpa [Matrix.mulVec_single_one] using h1⟩
  · rintro ⟨h20, h21⟩ v
    rw [burnsideF4f_mem_coordinateSpace_two, burnsideF4f_mem_coordinateSpace_two]
    have hdet : g.val.det ≠ 0 := by
      have := g.isUnit
      exact (Matrix.isUnit_iff_isUnit_det _).mp this |>.ne_zero
    rw [Matrix.det_fin_three, h20, h21] at hdet
    have h22 : g.val 2 2 ≠ 0 := fun h => hdet (by rw [h]; ring)
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h20, h21]
    constructor
    · intro e
      have : g.val 2 2 * v 2 = 0 := by linear_combination e
      exact (mul_eq_zero.mp this).resolve_left h22
    · intro e
      simp [e]

theorem burnsideF4f_mem_nativeBorel_L3 (q : ℕ) (g : nativeGroup .L3 q K) :
    g ∈ nativeBorel .L3 q K 1 ↔
      (g : GL (Fin 3) K).val 1 0 = 0 ∧ (g : GL (Fin 3) K).val 2 0 = 0 ∧
        (g : GL (Fin 3) K).val 2 1 = 0 := by
  unfold nativeBorel nativeParabolic
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.coe_subtype, Bool.false_eq_true,
    if_false, if_true]
  rw [burnsideF4f_stab_one, burnsideF4f_stab_two]
  tauto

theorem burnsideF4f_mem_StatedSL {n : ℕ} (g : GL (Fin n) K) :
    g ∈ StatedSL n K ↔ (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  have h : (Subgroup.closure {A : GL (Fin n) K | (A : Matrix (Fin n) (Fin n) K).det = 1}) =
      Matrix.GeneralLinearGroup.det.ker := by
    rw [← Subgroup.closure_eq (Matrix.GeneralLinearGroup.det (n := Fin n) (R := K)).ker]
    congr 1
    ext A
    simp [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply]
  unfold StatedSL
  rw [h]
  simp [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply]

theorem burnsideF4f_add_self_matrix [CharP K 2] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    A + A = 0 := by
  rw [← two_smul K A, CharTwo.two_eq_zero, zero_smul]

theorem burnsideF4f_sq_zero [CharP K 2] {A : Matrix (Fin 3) (Fin 3) K} (hA : A * A = 1) :
    (A - 1) * (A - 1) = 0 := by
  have h1 : (A - 1) * (A - 1) = A * A - (A + A) + 1 := by noncomm_ring
  rw [h1, hA, burnsideF4f_add_self_matrix, sub_zero]
  have := burnsideF4f_add_self_matrix (K := K) (1 : Matrix (Fin 3) (Fin 3) K)
  exact this

theorem burnsideF4f_exists_kernel_vec {N : Matrix (Fin 3) (Fin 3) K} (hNN : N * N = 0)
    {v : Fin 3 → K} (hv : v ≠ 0) (hNv : N.mulVec v = 0) :
    ∃ w : Fin 3 → K, N.mulVec w = 0 ∧ ∀ c : K, w ≠ c • v := by
  let f : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := Matrix.mulVecLin N
  have hf : ∀ x, f (f x) = 0 := by
    intro x
    show N.mulVec (N.mulVec x) = 0
    rw [Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  have hrk : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨x, rfl⟩
    exact hf x
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at h1
  have h2 : Module.finrank K (LinearMap.range f) ≤ Module.finrank K (LinearMap.ker f) :=
    Submodule.finrank_mono hrk
  have h3 : 2 ≤ Module.finrank K (LinearMap.ker f) := by omega
  have hspan : Submodule.span K {v} ≤ LinearMap.ker f := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact hNv
  have hnle : ¬ LinearMap.ker f ≤ Submodule.span K {v} := by
    intro hle
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hv] at this
    omega
  obtain ⟨w, hw, hwn⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨w, hw, fun c hc => hwn ?_⟩
  rw [hc]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

theorem burnsideF4f_invol_conj [CharP K 2] {A : Matrix (Fin 3) (Fin 3) K} (hA : A * A = 1)
    (hne : A ≠ 1) :
    ∃ Pm : Matrix (Fin 3) (Fin 3) K, Pm.det = 1 ∧ A * Pm = Pm * (1 + matrixUnit 0 2 1) := by
  set N := A - 1 with hNdef
  have hNN : N * N = 0 := burnsideF4f_sq_zero hA
  have hAN : A = 1 + N := by rw [hNdef]; abel
  have hN0 : N ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra h
    exact hN0 (by ext i j; by_contra hij; exact h ⟨i, j, hij⟩)
  set u : Fin 3 → K := Pi.single j 1 with hu
  set v : Fin 3 → K := N.mulVec u with hvdef
  have hv0 : v ≠ 0 := by
    intro h
    have := congrFun h i
    simp only [hvdef, hu, Matrix.mulVec_single_one, Pi.zero_apply] at this
    exact hij this
  have hNv : N.mulVec v = 0 := by rw [hvdef, Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  obtain ⟨w, hNw, hwv⟩ := burnsideF4f_exists_kernel_vec hNN hv0 hNv
  set Pmat : Matrix (Fin 3) (Fin 3) K := Matrix.of fun r k => ![v r, w r, u r] k with hPmat
  have hmul : ∀ c : Fin 3 → K, Pmat.mulVec c = c 0 • v + c 1 • w + c 2 • u := by
    intro c
    ext r
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hPmat, Matrix.vecHead, Matrix.vecTail]
    ring
  have hdet : Pmat.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hmul] at hc
    have h1 : N.mulVec (c 0 • v + c 1 • w + c 2 • u) = c 2 • v := by
      rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.mulVec_smul, hNv, hNw]
      simp [hvdef]
    rw [hc, Matrix.mulVec_zero] at h1
    have hc2 : c 2 = 0 := by
      by_contra h2
      exact hv0 ((smul_eq_zero.mp h1.symm).resolve_left h2)
    rw [hc2, zero_smul, add_zero] at hc
    have hc1 : c 1 = 0 := by
      by_contra h1'
      apply hwv (-(c 1)⁻¹ * c 0)
      have : c 1 • w = -(c 0 • v) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hc
      calc w = (c 1)⁻¹ • (c 1 • w) := by rw [smul_smul, inv_mul_cancel₀ h1', one_smul]
        _ = (c 1)⁻¹ • -(c 0 • v) := by rw [this]
        _ = (-(c 1)⁻¹ * c 0) • v := by rw [smul_neg, smul_smul, neg_mul, neg_smul]
    rw [hc1, zero_smul, add_zero] at hc
    have hc0' : c 0 = 0 := by
      by_contra h0'
      exact hv0 ((smul_eq_zero.mp hc).resolve_left h0')
    apply hc0
    ext k
    fin_cases k
    · exact hc0'
    · exact hc1
    · exact hc2
  set D := Pmat.det with hD
  set Pm : Matrix (Fin 3) (Fin 3) K := Pmat * Matrix.diagonal ![1, D⁻¹, 1] with hPm
  have hPm0 : ∀ r, Pm r 0 = v r := by
    intro r
    simp [hPm, hPmat, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_three]
  have hPm1 : ∀ r, Pm r 1 = D⁻¹ * w r := by
    intro r
    simp [hPm, hPmat, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_three, mul_comm]
  have hPm2 : ∀ r, Pm r 2 = u r := by
    intro r
    simp [hPm, hPmat, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_three]
  refine ⟨Pm, ?_, ?_⟩
  · rw [hPm, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three]
    simp
    exact mul_inv_cancel₀ hdet
  · have hNvi : ∀ r, ∑ l, N r l * v l = 0 := fun r => congrFun hNv r
    have hNwi : ∀ r, ∑ l, N r l * w l = 0 := fun r => congrFun hNw r
    have hNui : ∀ r, ∑ l, N r l * u l = v r := fun r => by
      simpa [Matrix.mulVec, dotProduct] using (congrFun hvdef r).symm
    rw [hAN, add_mul, one_mul]
    ext r k
    fin_cases k
    · simp [Matrix.add_apply, Matrix.mul_apply, hPm0, matrixUnit, Fin.sum_univ_three, hNvi r,
        Matrix.one_apply]
    · have h := hNwi r
      rw [Fin.sum_univ_three] at h
      simp [Matrix.add_apply, Matrix.mul_apply, hPm1, matrixUnit, Fin.sum_univ_three,
        Matrix.one_apply]
      linear_combination D⁻¹ * h
    · have h := hNui r
      rw [Fin.sum_univ_three] at h
      simp [Matrix.add_apply, Matrix.mul_apply, hPm2, matrixUnit, Fin.sum_univ_three,
        Matrix.one_apply]
      rw [hPm0]
      linear_combination h

@[expose] def burnsideF4f_mkSL (M : Matrix (Fin 3) (Fin 3) K) (h : M.det = 1) :
    ↥(StatedSL 3 K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [h]; exact one_ne_zero),
    (burnsideF4f_mem_StatedSL _).mpr (by simpa using h)⟩

theorem burnsideF4f_mkSL_val (M : Matrix (Fin 3) (Fin 3) K) (h : M.det = 1) :
    ((burnsideF4f_mkSL M h : ↥(StatedSL 3 K)) : GL (Fin 3) K).val = M := rfl

theorem burnsideF4f_det_T0 : (1 + matrixUnit 0 2 (1 : K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [Matrix.det_fin_three, matrixUnit, Matrix.one_apply]

@[expose] def burnsideF4f_T0 (K : Type) [Field K] : ↥(StatedSL 3 K) :=
  burnsideF4f_mkSL (1 + matrixUnit 0 2 1) burnsideF4f_det_T0

theorem burnsideF4f_T0_val :
    ((burnsideF4f_T0 K : ↥(StatedSL 3 K)) : GL (Fin 3) K).val =
      (1 + matrixUnit 0 2 1 : Matrix (Fin 3) (Fin 3) K) := rfl

theorem burnsideF4f_T0_sq [CharP K 2] : burnsideF4f_T0 K * burnsideF4f_T0 K = 1 := by
  apply Subtype.ext
  apply Units.ext
  show ((burnsideF4f_T0 K : ↥(StatedSL 3 K)) : GL (Fin 3) K).val *
    ((burnsideF4f_T0 K : ↥(StatedSL 3 K)) : GL (Fin 3) K).val = 1
  rw [burnsideF4f_T0_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, matrixUnit, Matrix.one_apply] <;>
    first | exact CharTwo.add_self_eq_zero (1 : K) | skip

variable {E : Type} [Group E]

theorem burnsideF4f_scalar_mem {s : K} (hs : s ≠ 0) (h : (s • (1 : Matrix (Fin 3) (Fin 3) K)).det = 1) :
    (burnsideF4f_mkSL (s • (1 : Matrix (Fin 3) (Fin 3) K)) h : GL (Fin 3) K) ∈
      StatedScalars (Fin 3) K := by
  refine ⟨Units.mk0 s hs, ?_⟩
  apply Units.ext
  simp [burnsideF4f_mkSL_val, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem burnsideF4f_L3_lift (φ : ↥(StatedSL 3 K) →* E) (hsurj : Function.Surjective φ)
    (hker : ∀ g : ↥(StatedSL 3 K), φ g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K)
    {x : E} (hx2 : x * x = 1) :
    ∃ A : ↥(StatedSL 3 K), φ A = x ∧
      (A : GL (Fin 3) K).val * (A : GL (Fin 3) K).val = 1 := by
  obtain ⟨B, hB⟩ := hsurj x
  have h1 : φ (B * B) = 1 := by rw [map_mul, hB, hx2]
  obtain ⟨c, hc⟩ : ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c =
      ((B * B : ↥(StatedSL 3 K)) : GL (Fin 3) K) := (hker _).mp h1
  have hcM : ((B : GL (Fin 3) K).val * (B : GL (Fin 3) K).val : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • 1 := by
    have := congrArg Units.val hc
    simpa [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using this.symm
  have hdetB : (B : GL (Fin 3) K).val.det = 1 := (burnsideF4f_mem_StatedSL _).mp B.2
  have hc3 : (c : K) ^ 3 = 1 := by
    have := congrArg Matrix.det hcM
    rw [Matrix.det_mul, hdetB, Matrix.det_smul, Matrix.det_one] at this
    simpa using this.symm
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  set s : K := ((c : K) ^ 2)⁻¹ with hs
  have hs0 : s ≠ 0 := inv_ne_zero (pow_ne_zero 2 hc0)
  have hs3 : s ^ 3 = 1 := by
    rw [hs, inv_pow, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hc3]; simp
  have hs2c : s ^ 2 * (c : K) = 1 := by
    have hc4 : (c : K) ^ 4 = (c : K) := by
      calc (c : K) ^ 4 = (c : K) * (c : K) ^ 3 := by ring
        _ = (c : K) := by rw [hc3, mul_one]
    rw [hs, inv_pow, ← pow_mul]
    show ((c : K) ^ 4)⁻¹ * (c : K) = 1
    rw [hc4]
    exact inv_mul_cancel₀ hc0
  have hdetS : (s • (1 : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
    rw [Matrix.det_smul, Matrix.det_one]; simpa using hs3
  let S : ↥(StatedSL 3 K) := burnsideF4f_mkSL (s • (1 : Matrix (Fin 3) (Fin 3) K)) hdetS
  have hdetA : (s • (B : GL (Fin 3) K).val).det = 1 := by
    rw [Matrix.det_smul, hdetB]; simpa using hs3
  let A : ↥(StatedSL 3 K) := burnsideF4f_mkSL (s • (B : GL (Fin 3) K).val) hdetA
  have hA : A = S * B := by
    apply Subtype.ext
    apply Units.ext
    show (s • (B : GL (Fin 3) K).val) = (s • (1 : Matrix (Fin 3) (Fin 3) K)) * (B : GL (Fin 3) K).val
    rw [smul_mul_assoc, one_mul]
  refine ⟨A, ?_, ?_⟩
  · rw [hA, map_mul, (hker S).mpr (burnsideF4f_scalar_mem hs0 hdetS), one_mul, hB]
  · show (s • (B : GL (Fin 3) K).val) * (s • (B : GL (Fin 3) K).val) = 1
    have hss : s * s * (c : K) = 1 := by rw [← hs2c]; ring
    rw [smul_mul_smul_comm, hcM, smul_smul, hss, one_smul]

theorem burnsideF4f_L3_isConj [CharP K 2] (φ : ↥(StatedSL 3 K) →* E)
    (hsurj : Function.Surjective φ)
    (hker : ∀ g : ↥(StatedSL 3 K), φ g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K)
    {x : E} (hx1 : x ≠ 1) (hx2 : x * x = 1) : IsConj (φ (burnsideF4f_T0 K)) x := by
  obtain ⟨A, hA, hAA⟩ := burnsideF4f_L3_lift φ hsurj hker hx2
  have hAne : (A : GL (Fin 3) K).val ≠ 1 := by
    intro h
    apply hx1
    rw [← hA]
    have : A = 1 := Subtype.ext (Units.ext h)
    rw [this, map_one]
  obtain ⟨Pm, hdet, hPm⟩ := burnsideF4f_invol_conj hAA hAne
  let P : ↥(StatedSL 3 K) := burnsideF4f_mkSL Pm hdet
  have key : A * P = P * burnsideF4f_T0 K := by
    apply Subtype.ext
    apply Units.ext
    exact hPm
  have hconj : P * burnsideF4f_T0 K * P⁻¹ = A := by
    rw [← key]; group
  rw [isConj_iff]
  refine ⟨φ P, ?_⟩
  rw [← hA, ← hconj]
  simp [map_mul, map_inv]

theorem burnsideF4f_L3_T0_ne_one (φ : ↥(StatedSL 3 K) →* E)
    (hker : ∀ g : ↥(StatedSL 3 K), φ g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K) :
    φ (burnsideF4f_T0 K) ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := (hker _).mp h
  have h2 := congrArg (fun g : GL (Fin 3) K => g.val 0 2) hc
  simp [burnsideF4f_T0_val, Matrix.scalar_apply, matrixUnit, Matrix.one_apply,
    Matrix.diagonal_apply] at h2

def burnsideF4f_B0 (K : Type) [Field K] : Subgroup ↥(StatedSL 3 K) :=
  nativeBorel .L3 2 K 1

theorem burnsideF4f_mem_B0 (g : ↥(StatedSL 3 K)) :
    g ∈ burnsideF4f_B0 K ↔
      (g : GL (Fin 3) K).val 1 0 = 0 ∧ (g : GL (Fin 3) K).val 2 0 = 0 ∧
        (g : GL (Fin 3) K).val 2 1 = 0 :=
  burnsideF4f_mem_nativeBorel_L3 2 g

theorem burnsideF4f_diag_mul {g h : Matrix (Fin 3) (Fin 3) K}
    (hg : g 1 0 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0) (hh : h 1 0 = 0 ∧ h 2 0 = 0 ∧ h 2 1 = 0)
    (i : Fin 3) : (g * h) i i = g i i * h i i := by
  obtain ⟨g10, g20, g21⟩ := hg
  obtain ⟨h10, h20, h21⟩ := hh
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three, g10, g20, g21, h10, h20, h21]

theorem burnsideF4f_B0_entries {g : ↥(StatedSL 3 K)} (hg : g ∈ burnsideF4f_B0 K) :
    (g : GL (Fin 3) K).val 1 0 = 0 ∧ (g : GL (Fin 3) K).val 2 0 = 0 ∧
      (g : GL (Fin 3) K).val 2 1 = 0 := (burnsideF4f_mem_B0 g).mp hg

theorem burnsideF4f_B0_diag_mul {g h : ↥(StatedSL 3 K)} (hg : g ∈ burnsideF4f_B0 K)
    (hh : h ∈ burnsideF4f_B0 K) (i : Fin 3) :
    ((g * h : ↥(StatedSL 3 K)) : GL (Fin 3) K).val i i =
      (g : GL (Fin 3) K).val i i * (h : GL (Fin 3) K).val i i :=
  burnsideF4f_diag_mul (burnsideF4f_B0_entries hg) (burnsideF4f_B0_entries hh) i

theorem burnsideF4f_B0_diag_pow {g : ↥(StatedSL 3 K)} (hg : g ∈ burnsideF4f_B0 K) (n : ℕ)
    (i : Fin 3) :
    ((g ^ n : ↥(StatedSL 3 K)) : GL (Fin 3) K).val i i = ((g : GL (Fin 3) K).val i i) ^ n := by
  induction n with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ, burnsideF4f_B0_diag_mul (Subgroup.pow_mem _ hg n) hg, ih, pow_succ]

theorem burnsideF4f_B0_det {g : ↥(StatedSL 3 K)} (hg : g ∈ burnsideF4f_B0 K) :
    (g : GL (Fin 3) K).val.det =
      (g : GL (Fin 3) K).val 0 0 * (g : GL (Fin 3) K).val 1 1 * (g : GL (Fin 3) K).val 2 2 := by
  obtain ⟨h10, h20, h21⟩ := burnsideF4f_B0_entries hg
  rw [Matrix.det_fin_three, h10, h20, h21]
  ring

theorem burnsideF4f_B0_diag_ne_zero {g : ↥(StatedSL 3 K)} (hg : g ∈ burnsideF4f_B0 K) (i : Fin 3) :
    (g : GL (Fin 3) K).val i i ≠ 0 := by
  have hd : (g : GL (Fin 3) K).val.det = 1 := (burnsideF4f_mem_StatedSL _).mp g.2
  rw [burnsideF4f_B0_det hg] at hd
  intro h0
  fin_cases i
  · rw [show (g : GL (Fin 3) K).val 0 0 = 0 from h0] at hd; simp at hd
  · rw [show (g : GL (Fin 3) K).val 1 1 = 0 from h0] at hd; simp at hd
  · rw [show (g : GL (Fin 3) K).val 2 2 = 0 from h0] at hd; simp at hd

theorem burnsideF4f_units_pow_inj [Finite K] [CharP K 2] {d e : Kˣ} {k : ℕ}
    (h : d ^ (2 ^ k) = e ^ (2 ^ k)) : d = e := by
  haveI := Fintype.ofFinite K
  have h1 : (d * e⁻¹) ^ (2 ^ k) = 1 := by
    rw [mul_pow, inv_pow, h, mul_inv_cancel]
  have h2 : orderOf (d * e⁻¹) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (d * e⁻¹) ∣ Nat.card Kˣ := orderOf_dvd_natCard _
  obtain ⟨n, hn2, hn⟩ := FiniteField.card K 2
  have hcard : Nat.card Kˣ = 2 ^ (n : ℕ) - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hn]
  have hodd : Odd (Nat.card Kˣ) := by
    rw [hcard]
    have hpos : 0 < (n : ℕ) := n.pos
    have : 2 ^ (n : ℕ) = 2 * 2 ^ ((n : ℕ) - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]
    have h2pos : 0 < 2 ^ ((n : ℕ) - 1) := by positivity
    exact ⟨2 ^ ((n : ℕ) - 1) - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ k) (Nat.card Kˣ) :=
    Nat.Coprime.pow_left _ hodd.coprime_two_left
  have h4 : orderOf (d * e⁻¹) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h3
  have h5 : d * e⁻¹ = 1 := orderOf_eq_one_iff.mp h4
  exact mul_inv_eq_one.mp h5

def burnsideF4f_U0 (K : Type) [Field K] : Subgroup ↥(StatedSL 3 K) where
  carrier := {g | g ∈ burnsideF4f_B0 K ∧ (g : GL (Fin 3) K).val 0 0 = 1 ∧
    (g : GL (Fin 3) K).val 1 1 = 1 ∧ (g : GL (Fin 3) K).val 2 2 = 1}
  one_mem' := ⟨one_mem _, by simp, by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha0, ha1, ha2⟩ ⟨hb, hb0, hb1, hb2⟩
    refine ⟨mul_mem ha hb, ?_, ?_, ?_⟩
    · rw [burnsideF4f_B0_diag_mul ha hb 0, ha0, hb0, one_mul]
    · rw [burnsideF4f_B0_diag_mul ha hb 1, ha1, hb1, one_mul]
    · rw [burnsideF4f_B0_diag_mul ha hb 2, ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨ha, ha0, ha1, ha2⟩
    have hai := inv_mem ha
    refine ⟨hai, ?_, ?_, ?_⟩
    · have := burnsideF4f_B0_diag_mul ha hai 0
      rw [mul_inv_cancel, ha0, one_mul] at this
      simpa using this.symm
    · have := burnsideF4f_B0_diag_mul ha hai 1
      rw [mul_inv_cancel, ha1, one_mul] at this
      simpa using this.symm
    · have := burnsideF4f_B0_diag_mul ha hai 2
      rw [mul_inv_cancel, ha2, one_mul] at this
      simpa using this.symm

theorem burnsideF4f_mem_U0 (g : ↥(StatedSL 3 K)) :
    g ∈ burnsideF4f_U0 K ↔ g ∈ burnsideF4f_B0 K ∧ (g : GL (Fin 3) K).val 0 0 = 1 ∧
      (g : GL (Fin 3) K).val 1 1 = 1 ∧ (g : GL (Fin 3) K).val 2 2 = 1 := Iff.rfl

theorem burnsideF4f_U0_le_B0 : burnsideF4f_U0 K ≤ burnsideF4f_B0 K := fun _ h => h.1

theorem burnsideF4f_U0_diag {u : ↥(StatedSL 3 K)} (hu : u ∈ burnsideF4f_U0 K) (i : Fin 3) :
    (u : GL (Fin 3) K).val i i = 1 := by
  fin_cases i
  · exact hu.2.1
  · exact hu.2.2.1
  · exact hu.2.2.2

theorem burnsideF4f_U0_conj {u b : ↥(StatedSL 3 K)} (hu : u ∈ burnsideF4f_U0 K)
    (hb : b ∈ burnsideF4f_B0 K) : b * u * b⁻¹ ∈ burnsideF4f_U0 K := by
  have hbi : b⁻¹ ∈ burnsideF4f_B0 K := inv_mem hb
  have hbu : b * u ∈ burnsideF4f_B0 K := mul_mem hb hu.1
  have key : ∀ i : Fin 3, ((b * u * b⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val i i = 1 := by
    intro i
    rw [burnsideF4f_B0_diag_mul hbu hbi i, burnsideF4f_B0_diag_mul hb hu.1 i,
      burnsideF4f_U0_diag hu i]
    have := burnsideF4f_B0_diag_mul hb hbi i
    rw [mul_inv_cancel] at this
    simp only [mul_one]
    simpa using this.symm
  exact ⟨mul_mem hbu hbi, key 0, key 1, key 2⟩

theorem burnsideF4f_unitri_pow_four [CharP K 2] {M : Matrix (Fin 3) (Fin 3) K}
    (h00 : M 0 0 = 1) (h11 : M 1 1 = 1) (h22 : M 2 2 = 1) (h10 : M 1 0 = 0) (h20 : M 2 0 = 0)
    (h21 : M 2 1 = 0) : M * M * (M * M) = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h4 : (4 : K) = 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this, h2, zero_mul]
  have h6 : (6 : K) = 0 := by
    have : (6 : K) = 2 * 3 := by norm_num
    rw [this, h2, zero_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h11, h22, h10, h20, h21, Matrix.one_apply] <;>
    ring_nf <;> simp [h2, h4, h6]

theorem burnsideF4f_U0_pow_four [CharP K 2] {u : ↥(StatedSL 3 K)} (hu : u ∈ burnsideF4f_U0 K) :
    u ^ 4 = 1 := by
  obtain ⟨h10, h20, h21⟩ := burnsideF4f_B0_entries hu.1
  have h := burnsideF4f_unitri_pow_four (K := K) (M := (u : GL (Fin 3) K).val)
    (burnsideF4f_U0_diag hu 0) (burnsideF4f_U0_diag hu 1) (burnsideF4f_U0_diag hu 2) h10 h20 h21
  have e : u ^ 4 = u * u * (u * u) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e]
  apply Subtype.ext
  apply Units.ext
  exact h

theorem burnsideF4f_L3_two_elements [Finite K] [CharP K 2] (φ : ↥(StatedSL 3 K) →* E)
    (hker : ∀ g : ↥(StatedSL 3 K), φ g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K)
    {x : E} (hx : x ∈ Subgroup.map φ (burnsideF4f_B0 K)) {k : ℕ} (hxk : x ^ (2 ^ k) = 1) :
    x ∈ Subgroup.map φ (burnsideF4f_U0 K) := by
  obtain ⟨g, hgB, rfl⟩ := hx
  have h1 : φ (g ^ (2 ^ k)) = 1 := by rw [map_pow, hxk]
  obtain ⟨c, hc⟩ : ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c =
      ((g ^ (2 ^ k) : ↥(StatedSL 3 K)) : GL (Fin 3) K) := (hker _).mp h1
  have hdiag : ∀ i : Fin 3, ((g : GL (Fin 3) K).val i i) ^ (2 ^ k) = (c : K) := by
    intro i
    have h2 := congrArg (fun m : GL (Fin 3) K => m.val i i) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h2
    rw [burnsideF4f_B0_diag_pow hgB] at h2
    simpa [Matrix.diagonal_apply] using h2.symm
  let d : Fin 3 → Kˣ := fun i => Units.mk0 _ (burnsideF4f_B0_diag_ne_zero hgB i)
  have hd : ∀ i, d i ^ (2 ^ k) = c := fun i => Units.ext (by simpa [d] using hdiag i)
  have hd01 : d 0 = d 1 := burnsideF4f_units_pow_inj ((hd 0).trans (hd 1).symm)
  have hd02 : d 0 = d 2 := burnsideF4f_units_pow_inj ((hd 0).trans (hd 2).symm)
  have hg1 : (g : GL (Fin 3) K).val 1 1 = (g : GL (Fin 3) K).val 0 0 := by
    have := congrArg Units.val hd01.symm
    simpa [d] using this
  have hg2 : (g : GL (Fin 3) K).val 2 2 = (g : GL (Fin 3) K).val 0 0 := by
    have := congrArg Units.val hd02.symm
    simpa [d] using this
  set d0 : K := (g : GL (Fin 3) K).val 0 0 with hd0
  have hd0ne : d0 ≠ 0 := burnsideF4f_B0_diag_ne_zero hgB 0
  have hdet : (g : GL (Fin 3) K).val.det = 1 := (burnsideF4f_mem_StatedSL _).mp g.2
  rw [burnsideF4f_B0_det hgB, hg1, hg2] at hdet
  have hd3 : d0 ^ 3 = 1 := by rw [← hdet]; ring
  have hdetS : (d0 • (1 : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
    rw [Matrix.det_smul, Matrix.det_one]; simpa using hd3
  have hdetg' : (d0⁻¹ • (g : GL (Fin 3) K).val).det = 1 := by
    rw [Matrix.det_smul, (burnsideF4f_mem_StatedSL _).mp g.2]
    simp only [Fintype.card_fin, mul_one, inv_pow, hd3, inv_one]
  let S : ↥(StatedSL 3 K) := burnsideF4f_mkSL (d0 • (1 : Matrix (Fin 3) (Fin 3) K)) hdetS
  let g' : ↥(StatedSL 3 K) := burnsideF4f_mkSL (d0⁻¹ • (g : GL (Fin 3) K).val) hdetg'
  have hgg : g = S * g' := by
    apply Subtype.ext
    apply Units.ext
    show (g : GL (Fin 3) K).val = (d0 • (1 : Matrix (Fin 3) (Fin 3) K)) *
      (d0⁻¹ • (g : GL (Fin 3) K).val)
    rw [smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ hd0ne, one_smul]
  obtain ⟨e10, e20, e21⟩ := burnsideF4f_B0_entries hgB
  have hg'B : g' ∈ burnsideF4f_B0 K := by
    rw [burnsideF4f_mem_B0]
    refine ⟨?_, ?_, ?_⟩ <;> simp [g', burnsideF4f_mkSL_val, e10, e20, e21]
  have hg'U : g' ∈ burnsideF4f_U0 K := by
    refine ⟨hg'B, ?_, ?_, ?_⟩
    · simp [g', burnsideF4f_mkSL_val, ← hd0, hd0ne]
    · simp [g', burnsideF4f_mkSL_val, hg1, ← hd0, hd0ne]
    · simp [g', burnsideF4f_mkSL_val, hg2, ← hd0, hd0ne]
  refine ⟨g', hg'U, ?_⟩
  rw [hgg, map_mul, (hker S).mpr (burnsideF4f_scalar_mem hd0ne hdetS), one_mul]

theorem burnsideF4f_U0_comm_of_phi (φ : ↥(StatedSL 3 K) →* E)
    (hker : ∀ g : ↥(StatedSL 3 K), φ g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3 ) K)
    {g u : ↥(StatedSL 3 K)} (hg : g ∈ burnsideF4f_U0 K) (hu : u ∈ burnsideF4f_U0 K)
    (h : φ g * φ u = φ u * φ g) : g * u = u * g := by
  have hc : g * u * g⁻¹ * u⁻¹ ∈ burnsideF4f_U0 K :=
    mul_mem (mul_mem (mul_mem hg hu) (inv_mem hg)) (inv_mem hu)
  have h1 : φ (g * u * g⁻¹ * u⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [h]; group
  obtain ⟨t, ht⟩ : ∃ t : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) t =
      ((g * u * g⁻¹ * u⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K) := (hker _).mp h1
  have ht1 : (t : K) = 1 := by
    have h2 := congrArg (fun m : GL (Fin 3) K => m.val 0 0) ht
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h2
    rw [burnsideF4f_U0_diag hc 0] at h2
    simpa using h2
  have h3 : g * u * g⁻¹ * u⁻¹ = 1 := by
    apply Subtype.ext
    rw [← ht]
    have : t = 1 := Units.ext ht1
    rw [this, map_one]
    rfl
  calc g * u = (g * u * g⁻¹ * u⁻¹) * (u * g) := by group
    _ = u * g := by rw [h3, one_mul]

theorem burnsideF4f_det_E01 : (1 + matrixUnit 0 1 (1 : K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [Matrix.det_fin_three, matrixUnit, Matrix.one_apply]

theorem burnsideF4f_det_E12 : (1 + matrixUnit 1 2 (1 : K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [Matrix.det_fin_three, matrixUnit, Matrix.one_apply]

theorem burnsideF4f_E01_mem : burnsideF4f_mkSL (1 + matrixUnit 0 1 (1 : K)) burnsideF4f_det_E01 ∈
    burnsideF4f_U0 K := by
  refine ⟨(burnsideF4f_mem_B0 _).mpr ?_, ?_, ?_, ?_⟩ <;>
    simp [burnsideF4f_mkSL_val, matrixUnit, Matrix.one_apply]

theorem burnsideF4f_E12_mem : burnsideF4f_mkSL (1 + matrixUnit 1 2 (1 : K)) burnsideF4f_det_E12 ∈
    burnsideF4f_U0 K := by
  refine ⟨(burnsideF4f_mem_B0 _).mpr ?_, ?_, ?_, ?_⟩ <;>
    simp [burnsideF4f_mkSL_val, matrixUnit, Matrix.one_apply]

theorem burnsideF4f_L3_central (φ : ↥(StatedSL 3 K) →* E)
    (hker : ∀ g : ↥(StatedSL 3 K), φ g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K)
    {g : ↥(StatedSL 3 K)} (hg : g ∈ burnsideF4f_U0 K)
    (hz : ∀ n ∈ Subgroup.map φ (burnsideF4f_U0 K), φ g * n = n * φ g) :
    (g : GL (Fin 3) K).val 0 1 = 0 ∧ (g : GL (Fin 3) K).val 1 2 = 0 := by
  have h1 := burnsideF4f_U0_comm_of_phi φ hker hg burnsideF4f_E01_mem
    (hz _ (Subgroup.mem_map_of_mem φ burnsideF4f_E01_mem))
  have h2 := burnsideF4f_U0_comm_of_phi φ hker hg burnsideF4f_E12_mem
    (hz _ (Subgroup.mem_map_of_mem φ burnsideF4f_E12_mem))
  constructor
  · have := congrArg (fun m : ↥(StatedSL 3 K) => (m : GL (Fin 3) K).val 0 2) h2
    simp [burnsideF4f_mkSL_val, matrixUnit, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, mul_add, add_mul] at this
    exact this
  · have := congrArg (fun m : ↥(StatedSL 3 K) => (m : GL (Fin 3) K).val 0 2) h1
    simp [burnsideF4f_mkSL_val, matrixUnit, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, mul_add, add_mul] at this
    exact this

theorem burnsideF4f_L3_centralizer_le [CharP K 2] (φ : ↥(StatedSL 3 K) →* E)
    (hsurj : Function.Surjective φ)
    (hker : ∀ g : ↥(StatedSL 3 K), φ g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K)
    {g : ↥(StatedSL 3 K)} (hgU : g ∈ burnsideF4f_U0 K) (ha : (g : GL (Fin 3) K).val 0 1 = 0)
    (hc : (g : GL (Fin 3) K).val 1 2 = 0) (hb : (g : GL (Fin 3) K).val 0 2 ≠ 0) {x : E}
    (hx : x * φ g = φ g * x) : x ∈ Subgroup.map φ (burnsideF4f_B0 K) := by
  obtain ⟨h, rfl⟩ := hsurj x
  have h1 : φ (h * g * h⁻¹ * g⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hx]; group
  obtain ⟨t, ht⟩ : ∃ t : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) t =
      ((h * g * h⁻¹ * g⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K) := (hker _).mp h1
  have hmat : (h : GL (Fin 3) K).val * (g : GL (Fin 3) K).val * ((h⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val *
      ((g⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val = (t : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg Units.val ht
    simpa [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using this.symm
  have hGiG : ((g⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val * (g : GL (Fin 3) K).val = 1 := by
    have := congrArg (fun m : ↥(StatedSL 3 K) => (m : GL (Fin 3) K).val) (inv_mul_cancel g)
    simpa using this
  have hHiH : ((h⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val * (h : GL (Fin 3) K).val = 1 := by
    have := congrArg (fun m : ↥(StatedSL 3 K) => (m : GL (Fin 3) K).val) (inv_mul_cancel h)
    simpa using this
  have hconj : (h : GL (Fin 3) K).val * (g : GL (Fin 3) K).val *
      ((h⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val = (t : K) • (g : GL (Fin 3) K).val := by
    calc (h : GL (Fin 3) K).val * (g : GL (Fin 3) K).val * ((h⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val
        = ((h : GL (Fin 3) K).val * (g : GL (Fin 3) K).val *
            ((h⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val *
            ((g⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val) * (g : GL (Fin 3) K).val := by
          rw [mul_assoc _ ((g⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val, hGiG, mul_one]
      _ = (t : K) • (g : GL (Fin 3) K).val := by rw [hmat, smul_mul_assoc, one_mul]
  have htr : Matrix.trace ((h : GL (Fin 3) K).val * (g : GL (Fin 3) K).val *
      ((h⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val) = Matrix.trace (g : GL (Fin 3) K).val := by
    rw [Matrix.trace_mul_comm, ← mul_assoc, hHiH, one_mul]
  have hg0 := burnsideF4f_U0_diag hgU 0
  have hg1 := burnsideF4f_U0_diag hgU 1
  have hg2 := burnsideF4f_U0_diag hgU 2
  have htrg : Matrix.trace (g : GL (Fin 3) K).val = 3 := by
    rw [Matrix.trace_fin_three, hg0, hg1, hg2]; norm_num
  have h3 : (3 : K) ≠ 0 := by
    have : (3 : K) = 1 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      calc (3 : K) = 2 + 1 := by norm_num
        _ = 1 := by rw [h2, zero_add]
    rw [this]; exact one_ne_zero
  have ht1 : (t : K) = 1 := by
    rw [hconj, Matrix.trace_smul, htrg, smul_eq_mul] at htr
    have : ((t : K) - 1) * 3 = 0 := by linear_combination htr
    have := (mul_eq_zero.mp this).resolve_right h3
    linear_combination this
  have hcomm : (h : GL (Fin 3) K).val * (g : GL (Fin 3) K).val =
      (g : GL (Fin 3) K).val * (h : GL (Fin 3) K).val := by
    have e : (h : GL (Fin 3) K).val * (g : GL (Fin 3) K).val *
        ((h⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val = (g : GL (Fin 3) K).val := by
      rw [hconj, ht1, one_smul]
    calc (h : GL (Fin 3) K).val * (g : GL (Fin 3) K).val
        = (h : GL (Fin 3) K).val * (g : GL (Fin 3) K).val *
            (((h⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val * (h : GL (Fin 3) K).val) := by
          rw [hHiH, mul_one]
      _ = ((h : GL (Fin 3) K).val * (g : GL (Fin 3) K).val *
            ((h⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val) * (h : GL (Fin 3) K).val := by
          rw [mul_assoc _ ((h⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K).val]
      _ = (g : GL (Fin 3) K).val * (h : GL (Fin 3) K).val := by rw [e]
  obtain ⟨g10, g20, g21⟩ := burnsideF4f_B0_entries hgU.1
  have e12 := congrArg (fun m : Matrix (Fin 3) (Fin 3) K => m 1 2) hcomm
  have e22 := congrArg (fun m : Matrix (Fin 3) (Fin 3) K => m 2 2) hcomm
  have e01 := congrArg (fun m : Matrix (Fin 3) (Fin 3) K => m 0 1) hcomm
  simp only [Matrix.mul_apply, Fin.sum_univ_three, g10, g20, g21, ha, hc, hg0, hg1, hg2] at e12 e22 e01
  refine ⟨h, (burnsideF4f_mem_B0 h).mpr ⟨?_, ?_, ?_⟩, rfl⟩
  · have : (g : GL (Fin 3) K).val 0 2 * (h : GL (Fin 3) K).val 1 0 = 0 := by linear_combination e12
    exact (mul_eq_zero.mp this).resolve_left hb
  · have : (g : GL (Fin 3) K).val 0 2 * (h : GL (Fin 3) K).val 2 0 = 0 := by linear_combination e22
    exact (mul_eq_zero.mp this).resolve_left hb
  · have : (g : GL (Fin 3) K).val 0 2 * (h : GL (Fin 3) K).val 2 1 = 0 := by linear_combination -e01
    exact (mul_eq_zero.mp this).resolve_left hb

theorem burnsideF4f_transport_surjective {kind : ClassicalRoots.Kind} {p exponent : ℕ} {H : Type}
    [Group H] (marking : ClassicalRoots.Marking kind p exponent H) :
    Function.Surjective marking.transport := by
  intro h
  obtain ⟨x, hx⟩ := marking.identification.surjective h
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨g, hx⟩

theorem burnsideF4f_transport_eq_one_iff {kind : ClassicalRoots.Kind} {p exponent : ℕ} {H : Type}
    [Group H] (marking : ClassicalRoots.Marking kind p exponent H)
    (g : nativeGroup kind (p ^ exponent) marking.field) :
    marking.transport g = 1 ↔
      (g : GL (Coord kind) marking.field) ∈ StatedScalars (Coord kind) marking.field := by
  show marking.identification (projectiveMap kind (p ^ exponent) marking.field g) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  show (QuotientGroup.mk g : _ ⧸ _) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf

theorem burnsideF4f_charP_of_card {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  haveI := ringChar.charP K
  obtain ⟨n, hp', hn⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card, hK] at hn
  have hdvd : 2 ∣ ringChar K ^ (n : ℕ) := by
    rw [← hn]
    exact dvd_pow_self 2 (by omega)
  have : 2 = ringChar K :=
    (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp').mp (Nat.prime_two.dvd_of_dvd_pow hdvd)
  rw [this]
  infer_instance

theorem burnsideF4f_L3_chart_data' {f : ℕ} {E : Type} [Group E] {Gp : Subgroup E}
    (chart : NativeChart .L3 2 f Gp) (hGp : Gp = ⊤) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (φ : ↥(nativeGroup .L3 (2 ^ f) K) →* E),
      Function.Surjective φ ∧
      (∀ g : ↥(nativeGroup .L3 (2 ^ f) K),
        φ g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K) ∧
      chart.borel = Subgroup.map φ (nativeBorel .L3 (2 ^ f) K 1) ∧
      ∃ t : ↥(nativeGroup .L3 (2 ^ f) K),
        (t : GL (Fin 3) K).val = 1 + matrixUnit 0 2 1 ∧ φ t ∈ chart.longRoot := by
  obtain ⟨marking, h1, -, -, h4⟩ := burnsideF4f_L3_marking chart
  letI : Field marking.field := marking.fieldStructure
  haveI : Finite marking.field := marking.finiteField
  have hK : Nat.card marking.field = 2 ^ f := by
    have := marking.field_card
    simpa using this
  haveI : CharP marking.field 2 := burnsideF4f_charP_of_card marking.exponent_pos hK
  have hbasis : marking.basis = 1 := marking.basis_compatible
  refine ⟨marking.field, inferInstance, inferInstance, inferInstance,
    Gp.subtype.comp marking.transport, ?_, ?_, ?_, ?_⟩
  · intro e
    have he : e ∈ Gp := by rw [hGp]; exact Subgroup.mem_top e
    obtain ⟨g, hg⟩ := burnsideF4f_transport_surjective marking ⟨e, he⟩
    exact ⟨g, by simp [hg]⟩
  · intro g
    have := burnsideF4f_transport_eq_one_iff marking g
    rw [← this]
    simp
  · rw [h1]
    unfold ClassicalRoots.Marking.borel
    rw [Subgroup.map_map, hbasis]
  · have hmem : ∃ t : ↥(nativeGroup .L3 (2 ^ f) marking.field),
        t ∈ nativeRoot .L3 (2 ^ f) (1 : GL (Coord .L3) marking.field) .a13 false ∧
          (t : GL (Fin 3) marking.field).val = 1 + matrixUnit 0 2 1 := by
      refine ⟨⟨(burnsideF4f_T0 marking.field : ↥(StatedSL 3 marking.field)).1,
        (burnsideF4f_T0 marking.field).2⟩, ?_, ?_⟩
      · refine Subgroup.subset_closure ⟨Or.inr (Or.inr rfl), 1, 0, trivial, ?_⟩
        show ((burnsideF4f_T0 marking.field : ↥(StatedSL 3 marking.field)) :
          GL (Fin 3) marking.field).val = _
        rw [burnsideF4f_T0_val]
        simp [markedMatrix, positiveMatrix, linearRoot]
      · exact burnsideF4f_T0_val
    obtain ⟨t, ht, ht'⟩ := hmem
    refine ⟨t, ht', ?_⟩
    rw [h4]
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ ?_)
    rw [hbasis]
    exact ht

theorem burnsideF4f_L3_chart_data {f : ℕ} {E : Type} [Group E] {Gp : Subgroup E}
    (chart : NativeChart .L3 2 f Gp) (hGp : Gp = ⊤) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (φ : ↥(StatedSL 3 K) →* E),
      Function.Surjective φ ∧
      (∀ g : ↥(StatedSL 3 K), φ g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K) ∧
      chart.borel = Subgroup.map φ (burnsideF4f_B0 K) ∧
      φ (burnsideF4f_T0 K) ∈ chart.longRoot := by
  obtain ⟨K, hF, hfin, hch, φ, hs, hk, hb, t, ht, hl⟩ := burnsideF4f_L3_chart_data' chart hGp
  have htT : t = burnsideF4f_T0 K := by
    apply Subtype.ext
    apply Units.ext
    rw [ht]
    exact burnsideF4f_T0_val.symm
  exact ⟨K, hF, hfin, hch, φ, hs, hk, hb, htT ▸ hl⟩

end L3Entries

section L3Final

theorem burnsideF4f_pCoreOf_eq {E : Type} [Group E] {H U : Subgroup E} (hUH : U ≤ H)
    (hnorm : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (hU2 : IsPGroup 2 U)
    (hall : ∀ x ∈ H, ∀ k : ℕ, x ^ (2 ^ k) = 1 → x ∈ U) : pCoreOf 2 H = U := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨y, hy⟩
    have hk' : (y : ↥H) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    refine hall (y : E) y.2 k ?_
    have := congrArg Subtype.val hk'
    simpa using this
  · intro u hu
    refine ⟨⟨u, hUH hu⟩, ?_, rfl⟩
    have hN : (U.subgroupOf H).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hnorm (g : E) g.2 (n : E) hn
    have hmem : (U.subgroupOf H) ∈ {K : Subgroup ↥H | K.Normal ∧ IsPGroup 2 K} :=
      ⟨hN, hU2.comap_subtype⟩
    exact Subgroup.mem_sSup_of_mem hmem (Subgroup.mem_subgroupOf.mpr hu)

theorem burnsideF4f_U0_eq_one {K : Type} [Field K] {g : ↥(StatedSL 3 K)}
    (hg : g ∈ burnsideF4f_U0 K) (h01 : (g : GL (Fin 3) K).val 0 1 = 0)
    (h12 : (g : GL (Fin 3) K).val 1 2 = 0) (h02 : (g : GL (Fin 3) K).val 0 2 = 0) : g = 1 := by
  obtain ⟨h10, h20, h21⟩ := burnsideF4f_B0_entries hg.1
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideF4f_U0_diag hg, h01, h12, h02, h10, h20, h21, Matrix.one_apply]

theorem burnsideF4f_U0_comm_E02 {K : Type} [Field K] {g u : ↥(StatedSL 3 K)}
    (hg : g ∈ burnsideF4f_U0 K) (hu : u ∈ burnsideF4f_U0 K)
    (h01 : (g : GL (Fin 3) K).val 0 1 = 0) (h12 : (g : GL (Fin 3) K).val 1 2 = 0) :
    g * u = u * g := by
  obtain ⟨g10, g20, g21⟩ := burnsideF4f_B0_entries hg.1
  obtain ⟨u10, u20, u21⟩ := burnsideF4f_B0_entries hu.1
  apply Subtype.ext
  apply Units.ext
  show (g : GL (Fin 3) K).val * (u : GL (Fin 3) K).val =
    (u : GL (Fin 3) K).val * (g : GL (Fin 3) K).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, burnsideF4f_U0_diag hg, burnsideF4f_U0_diag hu,
      h01, h12, g10, g20, g21, u10, u20, u21] <;> ring

theorem burnsideF4f_L3_U0_normal {K : Type} [Field K] {E : Type} [Group E]
    (φ : ↥(StatedSL 3 K) →* E) :
    ∀ h ∈ Subgroup.map φ (burnsideF4f_B0 K), ∀ u ∈ Subgroup.map φ (burnsideF4f_U0 K),
      h * u * h⁻¹ ∈ Subgroup.map φ (burnsideF4f_U0 K) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨u, hu, rfl⟩
  exact ⟨b * u * b⁻¹, burnsideF4f_U0_conj hu hb, by simp [map_mul, map_inv]⟩

theorem burnsideF4f_L3_U0_isPGroup {K : Type} [Field K] [CharP K 2] {E : Type} [Group E]
    (φ : ↥(StatedSL 3 K) →* E) : IsPGroup 2 (Subgroup.map φ (burnsideF4f_U0 K)) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  rintro ⟨_, u, hu, rfl⟩
  refine ⟨2, Subtype.ext ?_⟩
  show φ u ^ 2 ^ 2 = 1
  rw [← map_pow]
  have : u ^ 2 ^ 2 = 1 := burnsideF4f_U0_pow_four hu
  rw [this, map_one]

theorem burnsideF4f_L3_pCore_B0 {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Group E]
    (φ : ↥(StatedSL 3 K) →* E)
    (hker : ∀ g : ↥(StatedSL 3 K), φ g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K) :
    pCoreOf 2 (Subgroup.map φ (burnsideF4f_B0 K)) = Subgroup.map φ (burnsideF4f_U0 K) :=
  burnsideF4f_pCoreOf_eq (Subgroup.map_mono burnsideF4f_U0_le_B0) (burnsideF4f_L3_U0_normal φ)
    (burnsideF4f_L3_U0_isPGroup φ) (fun _ hx _ hxk => burnsideF4f_L3_two_elements φ hker hx hxk)

theorem burnsideF4f_L3_clause5 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hGp : Gp = ⊤) :
    ∀ element ∈ ctr (pCoreOf 2 (M₁ ⊓ M₂)), element ≠ 1 →
      pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Subgroup.centralizer ({element} : Set E)) := by
  obtain ⟨K, hF, hfin, hch, φ, hsurj, hker, hb, -⟩ :=
    burnsideF4f_L3_chart_data hyp.toHypF_4_4g.chart hGp
  have hM : M₁ ⊓ M₂ = Subgroup.map φ (burnsideF4f_B0 K) := by
    have h1 := hyp.toHypF_4_4g.chart_matches.1
    have h2 : M₁ ⊓ M₂ = Gp ⊓ (M₁ ⊓ M₂) := by rw [hGp, top_inf_eq]
    rw [h2, h1, hb]
  rw [hM, burnsideF4f_L3_pCore_B0 φ hker]
  intro z hz hz1
  obtain ⟨⟨g, hgU, rfl⟩, hzC⟩ := hz
  have hcomm : ∀ n ∈ Subgroup.map φ (burnsideF4f_U0 K), φ g * n = n * φ g :=
    fun n hn => (Subgroup.mem_centralizer_iff.mp hzC n hn).symm
  obtain ⟨ha, hc⟩ := burnsideF4f_L3_central φ hker hgU hcomm
  have hb02 : (g : GL (Fin 3) K).val 0 2 ≠ 0 := by
    intro h02
    apply hz1
    rw [burnsideF4f_U0_eq_one hgU ha hc h02, map_one]
  have hCB : Subgroup.centralizer ({φ g} : Set E) ≤ Subgroup.map φ (burnsideF4f_B0 K) := fun x hx =>
    burnsideF4f_L3_centralizer_le φ hsurj hker hgU ha hc hb02 (Subgroup.mem_centralizer_singleton_iff.mp hx)
  have hUC : Subgroup.map φ (burnsideF4f_U0 K) ≤ Subgroup.centralizer ({φ g} : Set E) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      burnsideF4f_U0_comm_E02 hgU hu ha hc |>.symm]
  exact (burnsideF4f_pCoreOf_eq hUC (fun h hh => burnsideF4f_L3_U0_normal φ h (hCB hh))
    (burnsideF4f_L3_U0_isPGroup φ)
    (fun x hx _ hxk => burnsideF4f_L3_two_elements φ hker (hCB hx) hxk)).symm

theorem burnsideF4f_L3_clause1 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hGp : Gp = ⊤) :
    Set.ncard (InvClasses E) = 1 ∧
      ∀ element : E, element ≠ 1 → element * element = 1 →
        hyp.toHypF_4_4g.chart.RootInvolution false element := by
  obtain ⟨K, hF, hfin, hch, φ, hsurj, hker, hb, hT0⟩ :=
    burnsideF4f_L3_chart_data hyp.toHypF_4_4g.chart hGp
  have hT0ne := burnsideF4f_L3_T0_ne_one φ hker
  have hT0sq : φ (burnsideF4f_T0 K) * φ (burnsideF4f_T0 K) = 1 := by
    rw [← map_mul, burnsideF4f_T0_sq, map_one]
  refine ⟨?_, ?_⟩
  · rw [Set.ncard_eq_one]
    refine ⟨ConjClasses.mk (φ (burnsideF4f_T0 K)), ?_⟩
    ext C
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hxC, hx1, hx2⟩
      rw [← ConjClasses.mem_carrier_iff_mk_eq.mp hxC]
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr (burnsideF4f_L3_isConj φ hsurj hker hx1 hx2).symm
    · rintro rfl
      exact ⟨φ (burnsideF4f_T0 K), ConjClasses.mem_carrier_iff_mk_eq.mpr rfl, hT0ne, hT0sq⟩
  · intro x hx1 hx2
    obtain ⟨c, hc⟩ := isConj_iff.mp (burnsideF4f_L3_isConj φ hsurj hker hx1 hx2)
    refine ⟨by rw [hGp]; exact Subgroup.mem_top x, hx1, hx2, fun h => absurd h (by simp),
      c⁻¹, by rw [hGp]; exact Subgroup.mem_top _, ?_⟩
    have : c⁻¹ * x * c⁻¹⁻¹ = φ (burnsideF4f_T0 K) := by rw [← hc]; group
    rw [this]
    exact hT0

theorem burnsideF4f_F427_L3 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hGp : Gp = ⊤) :
    hyp.toHypF_4_4g.chart.Matches M₁ M₂ ∧
    (Set.ncard (InvClasses E) = 1 ∧
      ∀ element : E, element ≠ 1 → element * element = 1 →
        hyp.toHypF_4_4g.chart.RootInvolution false element) ∧
    (∀ element ∈ ctr (pCoreOf 2 (M₁ ⊓ M₂)), element ≠ 1 →
      pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Subgroup.centralizer ({element} : Set E))) :=
  ⟨hyp.toHypF_4_4g.chart_matches, burnsideF4f_L3_clause1 hyp hGp, burnsideF4f_L3_clause5 hyp hGp⟩

theorem burnsideF4f_F427_kind_L3 : burnsideF4f_F427_kind .L3 := by
  intro f E _ Gp M₁ M₂ hyp hGp chart
  obtain ⟨hM, h1, h5⟩ := burnsideF4f_F427_L3 hyp hGp
  refine ⟨hM, fun _ => h1, fun hk => absurd hk (by decide), fun h => absurd rfl h.1,
    fun h => absurd rfl h, fun _ => h5⟩

theorem burnsideF4f_F427partial_kind_L3 : burnsideF4f_F427partial_kind .L3 :=
  burnsideF4f_F427partial_kind_of_kind burnsideF4f_F427_kind_L3

end L3Final

end L3

end CFSG.ASVolI
