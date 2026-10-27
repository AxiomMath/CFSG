module

public import CFSG.Quasithin.Background.F918H3

public section

namespace CFSG.Quasithin

section AutSubTransfer

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {V Z : Subgroup W}

theorem resHomOn_injective_of_faithful (hLV : L ≤ stabSub V) (hfaith : L ⊓ centSub V = ⊥) :
    Function.Injective (resHomOn V hLV) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hc : (g : MulAut W) ∈ L ⊓ centSub V := by
    refine ⟨g.2, fun u hu => ?_⟩
    exact congrArg (fun φ : MulAut ↥V => ((φ ⟨u, hu⟩ : ↥V) : W)) hg
  rw [hfaith, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.2 (Subtype.ext hc)

theorem inf_centSub_eq_bot_of_isSimpleGroup (hS : IsSimpleGroup ↥L) (hLV : L ≤ stabSub V)
    (hne : ¬ L ≤ centSub V) : L ⊓ centSub V = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (resHomOn V hLV).ker with hk | hk
  · rw [eq_bot_iff]
    intro g hg
    have hmem : (⟨g, hg.1⟩ : ↥L) ∈ (resHomOn V hLV).ker := by
      rw [MonoidHom.mem_ker]
      ext u
      exact hg.2 u u.2
    rw [hk, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hmem)
  · exfalso
    refine hne fun g hg u hu => ?_
    have hmem : (⟨g, hg⟩ : ↥L) ∈ (resHomOn V hLV).ker := by rw [hk]; trivial
    rw [MonoidHom.mem_ker] at hmem
    exact congrArg (fun φ : MulAut ↥V => ((φ ⟨u, hu⟩ : ↥V) : W)) hmem

@[expose] noncomputable def autSubEquivOfFaithful (hLV : L ≤ stabSub V)
    (hfaith : L ⊓ centSub V = ⊥) : ↥L ≃* ↥(autSub L V) :=
  (MonoidHom.ofInjective (resHomOn_injective_of_faithful hLV hfaith)).trans
    (MulEquiv.subgroupCongr (autSub_eq_range_resHomOn hLV).symm)

theorem autSubEquivOfFaithful_apply (hLV : L ≤ stabSub V) (hfaith : L ⊓ centSub V = ⊥)
    (g : ↥L) :
    ((autSubEquivOfFaithful hLV hfaith g : ↥(autSub L V)) : MulAut ↥V) = resHomOn V hLV g :=
  rfl

theorem FFModel.RealizesVia.of_autSub (hLV : L ≤ stabSub V) (hLZ : L ≤ stabSub Z) (hZV : Z ≤ V)
    (hfaith : L ⊓ centSub V = ⊥) {D : FFModel} {π : D.Gam →* ↥(autSub L V)}
    (h : D.RealizesVia (autSub L V) ⊤ (Z.subgroupOf V) π) :
    D.RealizesVia L V Z ((autSubEquivOfFaithful hLV hfaith).symm.toMonoidHom.comp π) := by
  obtain ⟨hsurj, -, hkerle, -, -, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  set e := autSubEquivOfFaithful hLV hfaith with he
  let q : ↥V →* ↥(⊤ : Subgroup ↥V) := (Subgroup.topEquiv (G := ↥V)).symm.toMonoidHom
  have hq_surj : Function.Surjective q := (Subgroup.topEquiv (G := ↥V)).symm.surjective
  refine ⟨e.symm.surjective.comp hsurj, hZV, hkerle, fun g u hu => (hLV g.2 u).2 hu,
    fun g z hz => (hLZ g.2 z).2 hz, hsec, hkerinv, β.comp q, hβs.comp hq_surj, ?_, ?_⟩
  · intro u
    rw [MonoidHom.comp_apply, hβk]
    exact Subgroup.mem_subgroupOf
  · intro γ u m hu hm hum
    have hπ : ((π γ : ↥(autSub L V)) : MulAut ↥V) = resHomOn V hLV (e.symm (π γ)) := by
      have := autSubEquivOfFaithful_apply hLV hfaith (e.symm (π γ))
      rw [← he, MulEquiv.apply_symm_apply] at this
      exact this
    have key := hβe γ (q u) m trivial hm hum
    have hqu : (⟨((π γ : ↥(autSub L V)) : MulAut ↥V) ((q u : ↥(⊤ : Subgroup ↥V)) : ↥V), trivial⟩ :
        ↥(⊤ : Subgroup ↥V)) = q ⟨((e.symm (π γ) : ↥L) : MulAut W) (u : W), hu⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hπ]
      rfl
    show β (q ⟨((e.symm (π γ) : ↥L) : MulAut W) (u : W), hu⟩) = _
    rw [← hqu]
    exact key

theorem FFModel.Realizes.of_autSub (hLV : L ≤ stabSub V) (hLZ : L ≤ stabSub Z) (hZV : Z ≤ V)
    (hfaith : L ⊓ centSub V = ⊥) {D : FFModel}
    (h : D.Realizes (autSub L V) ⊤ (Z.subgroupOf V)) : D.Realizes L V Z := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨_, FFModel.RealizesVia.of_autSub hLV hLZ hZV hfaith hπ⟩

theorem binaryNaturalSL_of_autSub (hLV : L ≤ stabSub V) (hLZ : L ≤ stabSub Z) (hZV : Z ≤ V)
    (hfaith : L ⊓ centSub V = ⊥) {d a : ℕ}
    (h : BinaryNaturalSL (autSub L V) ⊤ (Z.subgroupOf V) d a) : BinaryNaturalSL L V Z d a := by
  obtain ⟨K, hK, hf, hc, hr⟩ := h
  exact ⟨K, hK, hf, hc, FFModel.Realizes.of_autSub hLV hLZ hZV hfaith hr⟩

theorem binaryNaturalSz_of_autSub (hLV : L ≤ stabSub V) (hLZ : L ≤ stabSub Z) (hZV : Z ≤ V)
    (hfaith : L ⊓ centSub V = ⊥) {f : ℕ}
    (h : BinaryNaturalSz (autSub L V) ⊤ (Z.subgroupOf V) f) : BinaryNaturalSz L V Z f := by
  obtain ⟨a, ha, hfa, K, hK, hf, hc, hr⟩ := h
  exact ⟨a, ha, hfa, K, hK, hf, hc, FFModel.Realizes.of_autSub hLV hLZ hZV hfaith hr⟩

theorem binaryOrthogonalFour_of_autSub (hLV : L ≤ stabSub V) (hLZ : L ≤ stabSub Z) (hZV : Z ≤ V)
    (hfaith : L ⊓ centSub V = ⊥) {a : ℕ}
    (h : BinaryOrthogonalFour (autSub L V) ⊤ (Z.subgroupOf V) a) :
    BinaryOrthogonalFour L V Z a := by
  obtain ⟨K, hK, hf, hp, hc, hr⟩ := h
  exact ⟨K, hK, hf, hp, hc, FFModel.Realizes.of_autSub hLV hLZ hZV hfaith hr⟩

theorem alternatingNatural_of_autSub (hLV : L ≤ stabSub V) (hLZ : L ≤ stabSub Z) (hZV : Z ≤ V)
    (hfaith : L ⊓ centSub V = ⊥) {n : ℕ}
    (h : AlternatingNatural (autSub L V) ⊤ (Z.subgroupOf V) n) : AlternatingNatural L V Z n :=
  FFModel.Realizes.of_autSub hLV hLZ hZV hfaith h

end AutSubTransfer

end CFSG.Quasithin
