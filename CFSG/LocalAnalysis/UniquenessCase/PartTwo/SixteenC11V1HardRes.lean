module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

theorem s16c11_v1_resHom_injective {W : Type} [CommGroup W] {X K L : Subgroup (MulAut W)}
    {J₀ : Subgroup W} (hM : S16C11Model X K J₀) (hLX : L ≤ X)
    (hLK : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l) (hJ : ∀ l ∈ L, ∀ j ∈ J₀, l j ∈ J₀) :
    Function.Injective (CFSG.Quasithin.H13.VolI.resHom L J₀ hJ) := by
  obtain ⟨hJ', Θ, hΘ⟩ := s16c11_v1_model_pair hM hLX hLK
  have hJeq : hJ = hJ' := Subsingleton.elim _ _
  rw [hJeq]
  intro l₁ l₂ h
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  obtain ⟨p, rfl⟩ := Θ.surjective w
  rw [hΘ l₁ p, hΘ l₂ p, h]

theorem s16c11_v1_realizes_of_resHom {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {U : Subgroup W} (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U)
    (hinj : Function.Injective (CFSG.Quasithin.H13.VolI.resHom L U hU)) {D : FFModel}
    (h : D.Realizes (CFSG.Quasithin.H13.VolI.resHom L U hU).range ⊤ ⊥) :
    D.Realizes L U ⊥ := by
  obtain ⟨π, hπs, hZU, hkerle, hHU, hHZ, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  let f := CFSG.Quasithin.H13.VolI.resHom L U hU
  let ε : ↥L ≃* ↥f.range := MonoidHom.ofInjective hinj
  let π' : D.Gam →* ↥L := ε.symm.toMonoidHom.comp π
  let topIncl : ↥U →* ↥(⊤ : Subgroup ↥U) :=
    { toFun := fun u => ⟨u, Subgroup.mem_top u⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  let β' : ↥U →* ↥D.sec ⧸ D.ker.subgroupOf D.sec := β.comp topIncl
  have hcoe : ∀ (γ : D.Gam) (u : ↥U),
      ((π' γ : ↥L) : MulAut W) (u : W) =
        (((π γ : ↥f.range) : MulAut ↥U) u : W) := by
    intro γ u
    have h1 : f (π' γ) = (π γ : MulAut ↥U) :=
      congrArg Subtype.val (MulEquiv.apply_symm_apply ε (π γ))
    calc ((π' γ : ↥L) : MulAut W) (u : W)
        = (f (π' γ) u : W) :=
          (CFSG.Quasithin.H13.VolI.coe_resHom_apply L U hU (π' γ) u).symm
      _ = (((π γ : ↥f.range) : MulAut ↥U) u : W) := by rw [h1]
  have htop : Function.Surjective topIncl := fun v => ⟨(v : ↥U), Subtype.ext rfl⟩
  refine ⟨π', ?_, bot_le, hkerle, fun l u hu => hU l l.2 u hu, ?_, hsec, hkerinv,
    β', ?_, ?_, ?_⟩
  · intro l
    obtain ⟨γ, hγ⟩ := hπs (ε l)
    refine ⟨γ, ?_⟩
    show ε.symm (π γ) = l
    rw [hγ, MulEquiv.symm_apply_apply]
  · intro l z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · exact hβs.comp htop
  · intro u
    have h := hβk (topIncl u)
    change β (topIncl u) = 1 ↔ u ∈ (⊥ : Subgroup ↥U) at h
    rw [Subgroup.mem_bot] at h
    rw [Subgroup.mem_bot]
    change β (topIncl u) = 1 ↔ (u : W) = 1
    rw [h]
    exact Subtype.ext_iff
  · intro γ u m hu hm hum
    let u' : ↥(⊤ : Subgroup ↥U) := topIncl u
    have hcoe' : (u' : ↥U) = u := rfl
    have hhu' : ((π γ : ↥f.range) : MulAut ↥U) (u' : ↥U) ∈ (⊤ : Subgroup ↥U) :=
      Subgroup.mem_top _
    have hhum : β u' = QuotientGroup.mk m := by simpa [β', u'] using hum
    have hkey := hβe γ u' m hhu' hm hhum
    have hx : ((π' γ : ↥L) : MulAut W) (u : W) =
        (((π γ : ↥f.range) : MulAut ↥U) (u' : ↥U) : W) := by
      rw [hcoe γ u, ← hcoe']
    have hsub : topIncl ⟨((π' γ : ↥L) : MulAut W) (u : W), hu⟩ =
        ⟨((π γ : ↥f.range) : MulAut ↥U) (u' : ↥U), hhu'⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      exact hx
    simp only [β', MonoidHom.comp_apply]
    rw [hsub]
    exact hkey

theorem s16c11_v1_rf3_of_resHom {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    {U : Subgroup W} (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U)
    (hinj : Function.Injective (CFSG.Quasithin.H13.VolI.resHom L U hU))
    (h : S16C11RF3 (CFSG.Quasithin.H13.VolI.resHom L U hU).range (⊤ : Subgroup ↥U)) :
    S16C11RF3 L U := by
  intro T₀ hT₀L hT₀p hT₀i
  let f := CFSG.Quasithin.H13.VolI.resHom L U hU
  let Tbar : Subgroup (MulAut ↥U) := (T₀.subgroupOf L).map f
  have hTbarR : Tbar ≤ f.range := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact MonoidHom.mem_range.2 ⟨a, rfl⟩
  have hTbarp : IsPGroup 2 ↥Tbar :=
    IsPGroup.map (hT₀p.comap_of_injective L.subtype L.subtype_injective) f
  have h2 : (T₀.subgroupOf L).relIndex (⊤ : Subgroup ↥L) = T₀.relIndex L := by
    rw [← Subgroup.subgroupOf_self L]
    exact Subgroup.relIndex_subgroupOf (H := T₀) (K := L) (L := L) (le_refl L)
  have hrel : Tbar.relIndex f.range = T₀.relIndex L := by
    have h1 := Subgroup.relIndex_map_map_of_injective (T₀.subgroupOf L)
      (⊤ : Subgroup ↥L) hinj
    rw [← MonoidHom.range_eq_map f] at h1
    exact h1.trans h2
  have hTbari : ¬ 2 ∣ Tbar.relIndex f.range := by
    rw [hrel]
    exact hT₀i
  obtain ⟨Xbar, hXbarR, hTbarXbar, hidxbar, y, hy, hfixbar, g, hgXbar, hgybar⟩ :=
    h Tbar hTbarR hTbarp hTbari
  let X₀ : Subgroup (MulAut W) := (Xbar.comap f).map L.subtype
  have hX₀L : X₀ ≤ L := by
    intro x hx
    obtain ⟨l', -, rfl⟩ := Subgroup.mem_map.1 hx
    exact l'.2
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.1 (hXbarR hgXbar)
  refine ⟨X₀, hX₀L, ?_, ?_, (y : W), y.2, ?_, (l : MulAut W), ?_, ?_⟩
  · intro t ht
    refine Subgroup.mem_map.2 ⟨⟨t, hT₀L ht⟩, ?_, rfl⟩
    exact Subgroup.mem_comap.2 (hTbarXbar (Subgroup.mem_map.2
      ⟨⟨t, hT₀L ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩))
  · have hXsub : (X₀.subgroupOf L).map f = Xbar := by
      have h1 : X₀.subgroupOf L = Xbar.comap f := by
        show ((Xbar.comap f).map L.subtype).comap L.subtype = Xbar.comap f
        rw [Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
      rw [h1]
      exact Subgroup.map_comap_eq_self hXbarR
    have h2' : (T₀.subgroupOf L).relIndex (X₀.subgroupOf L) = T₀.relIndex X₀ :=
      Subgroup.relIndex_subgroupOf (H := T₀) (K := X₀) (L := L) hX₀L
    have h3 := Subgroup.relIndex_map_map_of_injective (T₀.subgroupOf L)
      (X₀.subgroupOf L) hinj
    rw [hXsub] at h3
    change Tbar.relIndex Xbar = (T₀.subgroupOf L).relIndex (X₀.subgroupOf L) at h3
    rw [hidxbar] at h3
    rw [h2'] at h3
    exact h3.symm
  · intro t ht
    have hmem : f ⟨t, hT₀L ht⟩ ∈ Tbar :=
      Subgroup.mem_map.2 ⟨⟨t, hT₀L ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
    have h := hfixbar (f ⟨t, hT₀L ht⟩) hmem
    have h2' := congrArg Subtype.val h
    rw [CFSG.Quasithin.H13.VolI.coe_resHom_apply] at h2'
    exact h2'
  · refine Subgroup.mem_map.2 ⟨l, ?_, rfl⟩
    rw [Subgroup.mem_comap, hl]
    exact hgXbar
  · intro hgy
    apply hgybar
    apply Subtype.ext
    rw [← hl]
    rw [CFSG.Quasithin.H13.VolI.coe_resHom_apply]
    exact hgy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
