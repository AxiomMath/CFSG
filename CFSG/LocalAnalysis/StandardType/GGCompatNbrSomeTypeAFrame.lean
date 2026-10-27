module

public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeTypeA

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank SpecialLinear Matrix

section Frames

variable {G : Type} [Group G] [Finite G]

theorem ggSecFiveCompat_of_endNodeAt {p : ℕ} {B : Subgroup G} {x : G} {L D J H : Subgroup G}
    {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G) (hφH : φ₁.range = H)
    (hker : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    {T : G} (hT : GGTypeAEndNode φ₁ T) (hHG : H ≤ ggG0 p B x L D J)
    (hTG : T ∈ ggG0 p B x L D J) (hL : L ≤ H ⊔ H.map (MulAut.conj T).toMonoidHom)
    (hnbr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      K ≤ H ⊔ H.map (MulAut.conj T).toMonoidHom) :
    ∃ ψ₀ : (ggU .PSL (n + 1 + 1) f).K →* G,
      GGPresentsG0 (ggG0 p B x L D J) (ggU .PSL (n + 1 + 1) f).D .PSL (n + 1 + 1) f ψ₀ ∧
        GGCompatPresented (ggU .PSL (n + 1 + 1) f).D ψ₀ H := by
  have h2 : (2 : GaloisField 2 f) = 0 := two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  have hHcl : H ≤ ggClosure (rootDatum (n + 1) (GaloisField 2 f))
      (fun _ : Unit => ggSupp (rootDatum (n + 1) (GaloisField 2 f)) (typeALeviJ (n + 1) (n + 1)))
      (fun _ => typeALeviHom φ₁) (typeAFrameLift h2 hT).range := by
    rw [← hφH, ← range_typeALeviHom]
    exact range_le_ggClosure (Δ := rootDatum (n + 1) (GaloisField 2 f))
      (S := fun _ : Unit =>
        ggSupp (rootDatum (n + 1) (GaloisField 2 f)) (typeALeviJ (n + 1) (n + 1)))
      (φ := fun _ => typeALeviHom φ₁) (R := (typeAFrameLift h2 hT).range) ()
  have hTR : T ∈ (typeAFrameLift h2 hT).range := ⟨_, typeAFrameLift_last h2 hT⟩
  have hHT : H.map (MulAut.conj T).toMonoidHom ≤ ggClosure (rootDatum (n + 1) (GaloisField 2 f))
      (fun _ : Unit => ggSupp (rootDatum (n + 1) (GaloisField 2 f)) (typeALeviJ (n + 1) (n + 1)))
      (fun _ => typeALeviHom φ₁) (typeAFrameLift h2 hT).range := by
    rw [← hφH, ← range_typeALeviHom]
    exact map_conj_le_ggClosure (Δ := rootDatum (n + 1) (GaloisField 2 f))
      (S := fun _ : Unit =>
        ggSupp (rootDatum (n + 1) (GaloisField 2 f)) (typeALeviJ (n + 1) (n + 1)))
      (φ := fun _ => typeALeviHom φ₁) (R := (typeAFrameLift h2 hT).range) ⟨T, hTR⟩ ()
  obtain ⟨ψ₀, hpres, hext⟩ := exists_presents_typeA_ext (m := n + 1) (k := n + 1) (by omega)
    le_rfl hf (typeALeviHom φ₁) (typeAFrameLift h2 hT) (typeAFrameLift_injective h2 hT hn hker)
    (fun j hj => typeAFrame_special h2 hT j hj) (typeAFrame_hcent h2 hT)
    (typeAFrame_hnt (by omega) hker) (by rw [range_typeALeviHom, hφH]; exact hHG)
    (typeAFrameLift_range_le h2 hT (hφH ▸ hHG) hTG) (hL.trans (sup_le hHcl hHT))
    (fun y K hK => (hnbr y K hK).trans (sup_le hHcl hHT))
  refine ⟨ψ₀, hpres, ?_⟩
  have hcomp : ψ₀.comp (slBlockHom n (GaloisField 2 f)) = φ₁ := by
    ext g
    have h1 := hext ⟨slBlockHom n (GaloisField 2 f) g, slBlockHom_mem g⟩
    rw [typeALeviHom_apply] at h1
    exact h1
  rw [← hφH, ← hcomp]
  exact ggCompatPresented_slBlock (by omega) hf hpres.2.1.2

theorem ggSecFiveCompat_of_twoEndNodesAt {p : ℕ} {B : Subgroup G} {x : G}
    {L D J H : Subgroup G} {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G) (hφH : φ₁.range = H)
    (hker : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    {T₁ T₂ : G} (hT : GGTypeATwoEndNodes φ₁ T₁ T₂) (hHG : H ≤ ggG0 p B x L D J)
    (hT₁G : T₁ ∈ ggG0 p B x L D J) (hT₂G : T₂ ∈ ggG0 p B x L D J)
    (hL : L ≤ H ⊔ H.map (MulAut.conj T₁).toMonoidHom ⊔ H.map (MulAut.conj (T₂ * T₁)).toMonoidHom ⊔
      H.map (MulAut.conj (T₁ * T₂ * T₁)).toMonoidHom)
    (hnbr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      K ≤ H ⊔ H.map (MulAut.conj T₁).toMonoidHom ⊔ H.map (MulAut.conj (T₂ * T₁)).toMonoidHom ⊔
        H.map (MulAut.conj (T₁ * T₂ * T₁)).toMonoidHom) :
    ∃ ψ₀ : (ggU .PSL (n + 1 + 1 + 1) f).K →* G,
      GGPresentsG0 (ggG0 p B x L D J) (ggU .PSL (n + 1 + 1 + 1) f).D .PSL (n + 1 + 1 + 1) f ψ₀ ∧
        GGCompatPresented (ggU .PSL (n + 1 + 1 + 1) f).D ψ₀ H := by
  have h2 : (2 : GaloisField 2 f) = 0 := two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  have hconj : ∀ r ∈ (typeAFrameLift₂ h2 hT).range,
      H.map (MulAut.conj r).toMonoidHom ≤ ggClosure (rootDatum (n + 1 + 1) (GaloisField 2 f))
        (fun _ : Unit =>
          ggSupp (rootDatum (n + 1 + 1) (GaloisField 2 f)) (typeALeviJ (n + 1 + 1) (n + 1)))
        (fun _ => typeALeviHom₂ φ₁) (typeAFrameLift₂ h2 hT).range := by
    intro r hr
    rw [← hφH, ← range_typeALeviHom₂]
    exact map_conj_le_ggClosure (Δ := rootDatum (n + 1 + 1) (GaloisField 2 f))
      (S := fun _ : Unit =>
        ggSupp (rootDatum (n + 1 + 1) (GaloisField 2 f)) (typeALeviJ (n + 1 + 1) (n + 1)))
      (φ := fun _ => typeALeviHom₂ φ₁) (R := (typeAFrameLift₂ h2 hT).range) ⟨r, hr⟩ ()
  have hHcl : H ≤ ggClosure (rootDatum (n + 1 + 1) (GaloisField 2 f))
      (fun _ : Unit =>
        ggSupp (rootDatum (n + 1 + 1) (GaloisField 2 f)) (typeALeviJ (n + 1 + 1) (n + 1)))
      (fun _ => typeALeviHom₂ φ₁) (typeAFrameLift₂ h2 hT).range := by
    rw [← hφH, ← range_typeALeviHom₂]
    exact range_le_ggClosure (Δ := rootDatum (n + 1 + 1) (GaloisField 2 f))
      (S := fun _ : Unit =>
        ggSupp (rootDatum (n + 1 + 1) (GaloisField 2 f)) (typeALeviJ (n + 1 + 1) (n + 1)))
      (φ := fun _ => typeALeviHom₂ φ₁) (R := (typeAFrameLift₂ h2 hT).range) ()
  have hT₁R : T₁ ∈ (typeAFrameLift₂ h2 hT).range :=
    ⟨_, typeAFrameLift₂_node_n h2 hT (show n < n + 1 + 1 by omega)⟩
  have hT₂₁R : T₂ * T₁ ∈ (typeAFrameLift₂ h2 hT).range :=
    ⟨(coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple ⟨n + 1, by omega⟩ *
      (coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple ⟨n, by omega⟩,
      by rw [map_mul, typeAFrameLift₂_node_succ h2 hT (show n + 1 < n + 1 + 1 by omega),
        typeAFrameLift₂_node_n h2 hT (show n < n + 1 + 1 by omega)]⟩
  have hT₁₂₁R : T₁ * T₂ * T₁ ∈ (typeAFrameLift₂ h2 hT).range :=
    mul_mem (mul_mem hT₁R ⟨_, typeAFrameLift₂_node_succ h2 hT (show n + 1 < n + 1 + 1 by omega)⟩)
      hT₁R
  have hjoin := sup_le (sup_le (sup_le hHcl (hconj T₁ hT₁R)) (hconj (T₂ * T₁) hT₂₁R))
    (hconj (T₁ * T₂ * T₁) hT₁₂₁R)
  obtain ⟨ψ₀, hpres, hext⟩ := exists_presents_typeA_ext (m := n + 1 + 1) (k := n + 1) (by omega)
    (by omega) hf (typeALeviHom₂ φ₁) (typeAFrameLift₂ h2 hT)
    (typeAFrameLift₂_injective h2 hT hn hker) (fun j hj => typeAFrame₂_special h2 hT j hj)
    (typeAFrame₂_hcent h2 hT) (typeAFrame₂_hnt (by omega) hker)
    (by rw [range_typeALeviHom₂, hφH]; exact hHG)
    (typeAFrameLift₂_range_le h2 hT (hφH ▸ hHG) hT₁G hT₂G) (hL.trans hjoin)
    (fun y K hK => (hnbr y K hK).trans hjoin)
  refine ⟨ψ₀, hpres, ?_⟩
  have hcomp : ψ₀.comp (slBlockHom₂ n (GaloisField 2 f)) = φ₁ := by
    ext g
    have h1 := hext ⟨slBlockHom₂ n (GaloisField 2 f) g, slBlockHom₂_mem g⟩
    rw [typeALeviHom₂_apply] at h1
    exact h1
  rw [← hφH, ← hcomp]
  exact ggCompatPresented_slBlock₂ (by omega) hf hpres.2.1.2

end Frames

section Configs

variable {G : Type} [Group G] [Finite G]

theorem ggSecFiveCompat_of_endNodeInput (hin : GGTypeAEndNodeInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} (hcfg : GGConfig p B Bs x L D J)
    (hOp : GGOpAutTrivial p Bs) (hInn : GGInnerDiagAll p B Bs x L D J)
    (hNoTr : GGNoTransvection p Bs) (hA : GGTypeASplitConfig p B Bs x L D J n f) :
    GGSecFiveCompat p B x L D J := by
  obtain ⟨hmod, hpq, hn, -⟩ := id hA
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hf1 : 1 ≤ f := hmod.1.2.1
  have hf : 2 ≤ f := by
    by_contra hlt
    have hf' : f = 1 := by omega
    rw [hf'] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  have hperf : commutator L = ⊤ := hcfg.1.2.2.2.2.2.2.2.1.1
  obtain ⟨φ₁, hφL, hker⟩ := exists_slLift_of_classicalModel (by omega) hf (by omega) hperf hmod
  obtain ⟨T, hTG, hT, hnbr⟩ := hin G p B Bs x L D J n f hcfg hOp hInn hNoTr hA φ₁ hφL hker
  obtain ⟨ψ₀, hpres, hcomp⟩ := ggSecFiveCompat_of_endNodeAt hn hf1 φ₁ hφL hker hT
    (le_ggG0_left p B x L D J) hTG le_sup_left hnbr
  exact ⟨.PSL, n + 1 + 1, f, ψ₀, hpres, L, Or.inl rfl, hcomp⟩

theorem ggSecFiveCompat_of_join (hE : GGTypeAJoinEndNodeInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (h : GGTypeANbr p B Bs x L D J n f y K)
    (hjoin : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ L ⊔ K) :
    GGSecFiveCompat p B x L D J := by
  obtain ⟨hf1, φ₁, hφL, hker⟩ := h.exists_lift hcfg
  obtain ⟨T, hTLK, hT, hKle⟩ := hE G p B Bs x L D J n f y K hcfg hOp hInn hNoTr h φ₁ hφL hker
  obtain ⟨ψ₀, hpres, hcomp⟩ := ggSecFiveCompat_of_endNodeAt h.2.2.1 hf1 φ₁ hφL hker hT
    (le_ggG0_left p B x L D J) (h.sup_le_ggG0 hTLK) le_sup_left
    (fun y' K' hK' => (hjoin y' K' hK').trans (sup_le le_sup_left hKle))
  exact ⟨.PSL, n + 1 + 1, f, ψ₀, hpres, L, Or.inl rfl, hcomp⟩

theorem ggSecFiveCompat_of_corankTwo (hE : GGTypeAJoinEndNodeInput)
    (hC : GGTypeACorankTwoInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} {y : G} {K : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hOp : GGOpAutTrivial p Bs) (hInn : GGInnerDiagAll p B Bs x L D J)
    (hNoTr : GGNoTransvection p Bs) (h : GGTypeANbr p B Bs x L D J n f y K) (hdiv : p ∣ n + 3)
    (hout : ∃ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' ∧ ¬ K' ≤ L ⊔ K) :
    GGSecFiveCompat p B x L D J := by
  obtain ⟨hf1, φ₁, hφL, hker⟩ := h.exists_lift hcfg
  obtain ⟨T₁, hT₁LK, hT₁, hKle⟩ := hE G p B Bs x L D J n f y K hcfg hOp hInn hNoTr h φ₁ hφL hker
  obtain ⟨T₂, hT₂G, hT, hnbr⟩ := hC G p B Bs x L D J n f y K hcfg hOp hInn hNoTr h hdiv hout φ₁
    hφL hker T₁ hT₁LK hT₁ hKle
  obtain ⟨ψ₀, hpres, hcomp⟩ := ggSecFiveCompat_of_twoEndNodesAt h.2.2.1 hf1 φ₁ hφL hker hT
    (le_ggG0_left p B x L D J) (h.sup_le_ggG0 hT₁LK) hT₂G
    (le_sup_left.trans (le_sup_left.trans le_sup_left)) hnbr
  exact ⟨.PSL, n + 1 + 1 + 1, f, ψ₀, hpres, L, Or.inl rfl, hcomp⟩

theorem ggSecFiveCompat_of_half (hH : GGTypeAHalfEndNodesInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n : ℕ} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (h : GGTypeAHalfNbr p B Bs x L D J n y K) : GGSecFiveCompat p B x L D J := by
  obtain ⟨φ₁, hφL, hker, T₁, T₂, hT₁G, hT₂G, hT, hnbr⟩ :=
    hH G p B Bs x L D J n y K hcfg hOp hInn hNoTr h
  obtain ⟨ψ₀, hpres, hcomp⟩ := ggSecFiveCompat_of_twoEndNodesAt
    (by have := h.2.2.1; omega) le_rfl φ₁ hφL hker hT (le_ggG0_left p B x L D J) hT₁G hT₂G
    (le_sup_left.trans (le_sup_left.trans le_sup_left)) hnbr
  exact ⟨.PSL, n + 1 + 1 + 1, 1, ψ₀, hpres, L, Or.inl rfl, hcomp⟩

end Configs

end CFSG.StandardType
