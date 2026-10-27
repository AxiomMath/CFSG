module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFinite

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {Q : Type} [Group Q] [Finite Q]

theorem sq_central_of_decomp_of_k1 {A : Subgroup Q} (hK1 : K1In ⊤ A) (hA : IsElemAbelian 2 A)
    {J : Subgroup Q} (hJ : IsComponentOf J ⊤) {a b s c : Q} (ha : a ∈ A) (hb : b ∈ A)
    (hmoved : conjSubgroup J a ≠ J) (hsJ : s ∈ J) (hs : s * s = 1)
    (hc : c ∈ centralizer (J : Set Q)) (hbsc : b = s * c) :
    ∀ w ∈ J, ∀ l ∈ J, ((s * (w * s * w⁻¹)) * (s * (w * s * w⁻¹))) * l =
      l * ((s * (w * s * w⁻¹)) * (s * (w * s * w⁻¹))) := by
  intro w hw l hl
  have haa : a * a = 1 := by simpa [pow_two] using hA.2 a ha
  have hab : a * b = b * a :=
    congrArg Subtype.val (hA.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have haba : a * b * a⁻¹ = b := by rw [hab]; group
  have ha1 : a ≠ 1 := fun h => hmoved (by rw [h, conjSubgroup_one])
  set J₂ : Subgroup Q := conjSubgroup J a⁻¹ with hJ₂_def
  have hJ₂ : IsComponentOf J₂ ⊤ := by
    rw [hJ₂_def]
    have hh := (CFSG.ComponentClassification.LocalComponents.equiv_iff
      (MulAut.conj a) J).mpr hJ
    simpa [conjSubgroup] using hh
  have hJ₂ne : J₂ ≠ J := by
    intro h
    have hconj : conjSubgroup J₂ a = conjSubgroup J (a⁻¹ * a) :=
      conjSubgroup_conjSubgroup J a⁻¹ a
    rw [h, inv_mul_cancel, conjSubgroup_one] at hconj
    exact hmoved hconj
  have hle1 : J ≤ Subgroup.centralizer (J₂ : Set Q) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne J J₂ hJ hJ₂
        (Ne.symm hJ₂ne))
  have hle2 : J₂ ≤ Subgroup.centralizer (J : Set Q) :=
    (Subgroup.le_centralizer_iff).mpr hle1
  have hcomm : ∀ p ∈ J, ∀ q ∈ J₂, Commute p q := fun p hp q hq =>
    Subgroup.mem_centralizer_iff.mp (hle2 hq) p hp
  set s' : Q := a * s * a⁻¹ with hs'_def
  set c' : Q := a * c * a⁻¹ with hc'_def
  set w' : Q := a * w * a⁻¹ with hw'_def
  have hs'J₂ : s' ∈ J₂ := by
    rw [hJ₂_def, mem_conjSubgroup_iff, hs'_def, inv_inv]
    rw [show a⁻¹ * (a * s * a⁻¹) * a = s by group]
    exact hsJ
  have hc'C' : ∀ y ∈ J₂, Commute c' y := by
    intro y hy
    have hmem : a⁻¹ * y * a ∈ J := by
      rw [hJ₂_def] at hy
      simpa using mem_conjSubgroup_iff.mp hy
    have hy_eq : y = a * (a⁻¹ * y * a) * a⁻¹ := by group
    have hc_mem : Commute (a⁻¹ * y * a) c :=
      Subgroup.mem_centralizer_iff.mp hc (a⁻¹ * y * a) hmem
    show c' * y = y * c'
    rw [hc'_def]
    calc (a * c * a⁻¹) * y = a * (c * (a⁻¹ * y * a)) * a⁻¹ := by rw [hy_eq]; group
      _ = a * ((a⁻¹ * y * a) * c) * a⁻¹ := by rw [← hc_mem.eq]
      _ = y * (a * c * a⁻¹) := by rw [hy_eq]; group
  have hs'c'_comm : Commute s' c' := (hc'C' s' hs'J₂).symm
  have hbsc' : b = s' * c' := by
    calc b = a * b * a⁻¹ := haba.symm
      _ = a * (s * c) * a⁻¹ := by rw [hbsc]
      _ = s' * c' := by rw [hs'_def, hc'_def]; group
  set d : Q := s * s' with hd_def
  set c₀ : Q := b * d⁻¹ with hc₀_def
  have hb_c₀d : b = c₀ * d := by rw [hc₀_def]; group
  have hc₀J : ∀ j ∈ J, Commute c₀ j := by
    intro j hj
    have hz : s⁻¹ * j * s ∈ J :=
      J.mul_mem (J.mul_mem (J.inv_mem hsJ) hj) hsJ
    have hs'_z : Commute s' (s⁻¹ * j * s) := (hcomm (s⁻¹ * j * s) hz s' hs'J₂).symm
    have hd_j_d : d⁻¹ * j * d = s⁻¹ * j * s := by
      rw [hd_def]
      calc (s * s')⁻¹ * j * (s * s') = s'⁻¹ * (s⁻¹ * j * s) * s' := by group
        _ = s⁻¹ * j * s := Commute.inv_mul_cancel hs'_z
    have hc_z : Commute c (s⁻¹ * j * s) :=
      (Subgroup.mem_centralizer_iff.mp hc (s⁻¹ * j * s) hz).symm
    have hb_j : b * (s⁻¹ * j * s) * b⁻¹ = j := by
      rw [hbsc, mul_inv_rev]
      calc (s * c) * (s⁻¹ * j * s) * (c⁻¹ * s⁻¹) =
            s * (c * (s⁻¹ * j * s) * c⁻¹) * s⁻¹ := by group
        _ = s * (s⁻¹ * j * s) * s⁻¹ := by rw [Commute.mul_inv_cancel hc_z]
        _ = j := by group
    show c₀ * j = j * c₀
    have h1 : c₀ * j * c₀⁻¹ = b * (d⁻¹ * j * d) * b⁻¹ := by rw [hc₀_def]; group
    calc c₀ * j = (c₀ * j * c₀⁻¹) * c₀ := by group
      _ = j * c₀ := by rw [h1, hd_j_d, hb_j]
  have hc₀J₂ : ∀ y ∈ J₂, Commute c₀ y := by
    intro y hy
    have hsy : s⁻¹ * y * s = y := Commute.inv_mul_cancel (hcomm s hsJ y hy)
    have hc'y : c' * y * c'⁻¹ = y := Commute.mul_inv_cancel (hc'C' y hy)
    have hc₀_eq2 : c₀ = c' * s⁻¹ := by
      rw [hc₀_def, hd_def, hbsc']
      calc (s' * c') * (s * s')⁻¹ = (s' * c' * s'⁻¹) * s⁻¹ := by group
        _ = c' * s⁻¹ := by rw [Commute.mul_inv_cancel hs'c'_comm]
    show c₀ * y = y * c₀
    have h1 : c₀ * y * c₀⁻¹ = c' * (s⁻¹ * y * s) * c'⁻¹ := by rw [hc₀_eq2]; group
    calc c₀ * y = (c₀ * y * c₀⁻¹) * c₀ := by group
      _ = y * c₀ := by rw [h1, hsy, hc'y]
  have hw'J₂ : w' ∈ J₂ := by
    rw [hJ₂_def, mem_conjSubgroup_iff, hw'_def, inv_inv]
    rw [show a⁻¹ * (a * w * a⁻¹) * a = w by group]
    exact hw
  set x : Q := w * w' with hx_def
  have hx_eq : x = w * w' := hx_def
  have hai : a⁻¹ = a := (eq_inv_of_mul_eq_one_right haa).symm
  have haw'a : a * w' * a⁻¹ = w := by
    rw [hw'_def]
    calc a * (a * w * a⁻¹) * a⁻¹ = (a * a) * w * (a⁻¹ * a⁻¹) := by group
      _ = w := by rw [haa, hai, haa]; group
  have hx_eq : x = w * w' := hx_def
  have hax_a : a * x * a⁻¹ = x := by
    rw [hx_def]
    calc a * (w * w') * a⁻¹ = (a * w * a⁻¹) * (a * w' * a⁻¹) := by group
      _ = w' * w := by rw [hw'_def.symm, haw'a]
      _ = w * w' := (hcomm w hw w' hw'J₂).symm.eq
  have hax_comm : x * a = a * x := by
    calc x * a = (a * x * a⁻¹) * a := by rw [hax_a]
      _ = a * x := by group
  set e : Q := s * (w * s * w⁻¹) with he_def
  set f : Q := s' * (w' * s' * w'⁻¹) with hf_def
  have heJ : e ∈ J := by
    rw [he_def]
    exact J.mul_mem hsJ (J.mul_mem (J.mul_mem hw hsJ) (J.inv_mem hw))
  have hfJ₂ : f ∈ J₂ := by
    rw [hf_def]
    exact J₂.mul_mem hs'J₂ (J₂.mul_mem (J₂.mul_mem hw'J₂ hs'J₂) (J₂.inv_mem hw'J₂))
  have hcx : Commute c₀ x := (hc₀J w hw).mul_right (hc₀J₂ w' hw'J₂)
  have hcd : Commute c₀ d := (hc₀J s hsJ).mul_right (hc₀J₂ s' hs'J₂)
  have hcommφ : ∀ m : ↥J, ∀ n : ↥J₂, Commute (J.subtype m) (J₂.subtype n) :=
    fun m n => by simpa using hcomm (m : Q) m.2 (n : Q) n.2
  let φ : ↥J × ↥J₂ →* Q := MonoidHom.noncommCoprod J.subtype J₂.subtype hcommφ
  have hφ : ∀ (p : ↥J) (q : ↥J₂), φ (p, q) = (p : Q) * (q : Q) := by
    intro p q
    dsimp only [φ]
    rw [MonoidHom.noncommCoprod_apply]
    rfl
  let P : ↥J × ↥J₂ := (⟨s, hsJ⟩, ⟨s', hs'J₂⟩)
  let W : ↥J × ↥J₂ := (⟨w, hw⟩, ⟨w', hw'J₂⟩)
  have hdφ : d = φ P := (hφ ⟨s, hsJ⟩ ⟨s', hs'J₂⟩).symm
  have hxφ : x = φ W := (hφ ⟨w, hw⟩ ⟨w', hw'J₂⟩).symm
  have hprod : P * W * P * W⁻¹ = (⟨e, heJ⟩, ⟨f, hfJ₂⟩) := by
    apply Prod.ext
    · apply Subtype.ext
      dsimp only [P, W]
      simp only [Prod.fst_mul, Prod.fst_inv, Subtype.coe_mk, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [he_def]
      group
    · apply Subtype.ext
      dsimp only [P, W]
      simp only [Prod.snd_mul, Prod.snd_inv, Subtype.coe_mk, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [hf_def]
      group
  have hdx : d * x * d * x⁻¹ = e * f := by
    calc d * x * d * x⁻¹
        = φ P * φ W * φ P * (φ W)⁻¹ := by rw [hdφ, hxφ]
      _ = φ (P * W * P * W⁻¹) := by rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
      _ = φ (⟨e, heJ⟩, ⟨f, hfJ₂⟩) := by rw [hprod]
      _ = e * f := hφ _ _
  have hbx : b * (x * b * x⁻¹) = e * f * (c₀ * c₀) := by
    rw [hb_c₀d]
    have step1 : x * (c₀ * d) * x⁻¹ = c₀ * (x * d * x⁻¹) := by
      calc x * (c₀ * d) * x⁻¹ = (x * c₀) * (d * x⁻¹) := by group
        _ = (c₀ * x) * (d * x⁻¹) := by rw [hcx.eq]
        _ = c₀ * (x * d * x⁻¹) := by group
    rw [step1]
    have step2 : (c₀ * d) * (c₀ * (x * d * x⁻¹)) =
        c₀ * c₀ * (d * x * d * x⁻¹) := by
      calc (c₀ * d) * (c₀ * (x * d * x⁻¹)) = c₀ * (d * c₀) * (x * d * x⁻¹) := by group
        _ = c₀ * (c₀ * d) * (x * d * x⁻¹) := by rw [hcd.eq.symm]
        _ = c₀ * c₀ * (d * x * d * x⁻¹) := by group
    rw [step2, hdx]
    have hcef : Commute c₀ (e * f) := (hc₀J e heJ).mul_right (hc₀J₂ f hfJ₂)
    exact (hcef.mul_left hcef).eq
  have hxC : x ∈ (⊤ : Subgroup Q) ⊓ centralizer ({a} : Set Q) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_top x, by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact hax_comm⟩
  have hmem_b : b ∈ Subgroup.closure {γ : Q |
      ∃ z ∈ (⊤ : Subgroup Q) ⊓ centralizer ({a} : Set Q), γ = z * b * z⁻¹} :=
    Subgroup.subset_closure ⟨1, Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_top 1, (centralizer ({a} : Set Q)).one_mem⟩, by group⟩
  have hmem_xb : x * b * x⁻¹ ∈ Subgroup.closure {γ : Q |
      ∃ z ∈ (⊤ : Subgroup Q) ⊓ centralizer ({a} : Set Q), γ = z * b * z⁻¹} :=
    Subgroup.subset_closure ⟨x, hxC, rfl⟩
  have hsq : (b * (x * b * x⁻¹)) * (b * (x * b * x⁻¹)) = 1 := by
    have h := (hK1 b hb a ha ha1).2 (b * (x * b * x⁻¹))
      ((Subgroup.closure _).mul_mem hmem_b hmem_xb)
    simpa [pow_two] using h
  have h1 : (e * f * (c₀ * c₀)) * (e * f * (c₀ * c₀)) = 1 := by
    rw [← hbx]; exact hsq
  have h1a : (e * (f * (c₀ * c₀))) * (e * (f * (c₀ * c₀))) = 1 := by
    rw [show e * f * (c₀ * c₀) = e * (f * (c₀ * c₀)) by group] at h1
    exact h1
  have he_c₀ : Commute e c₀ := (hc₀J e heJ).symm
  have he_g : Commute e (f * (c₀ * c₀)) :=
    (hcomm e heJ f hfJ₂).mul_right (he_c₀.mul_right he_c₀)
  have hee_gg : (e * e) * ((f * (c₀ * c₀)) * (f * (c₀ * c₀))) = 1 := by
    have h : (e * (f * (c₀ * c₀))) * (e * (f * (c₀ * c₀))) =
        (e * e) * ((f * (c₀ * c₀)) * (f * (c₀ * c₀))) := by
      calc (e * (f * (c₀ * c₀))) * (e * (f * (c₀ * c₀)))
          = e * ((f * (c₀ * c₀)) * e) * (f * (c₀ * c₀)) := by group
        _ = e * (e * (f * (c₀ * c₀))) * (f * (c₀ * c₀)) := by rw [he_g.symm.eq]
        _ = (e * e) * ((f * (c₀ * c₀)) * (f * (c₀ * c₀))) := by group
    rw [← h]; exact h1a
  have hgl : Commute ((f * (c₀ * c₀)) * (f * (c₀ * c₀))) l := by
    have hfc : Commute f l := (hcomm l hl f hfJ₂).symm
    have hcc : Commute (c₀ * c₀) l := (hc₀J l hl).mul_left (hc₀J l hl)
    have hg : Commute (f * (c₀ * c₀)) l := hfc.mul_left hcc
    exact hg.mul_left hg
  have hee_l : Commute (e * e) l := by
    have hee : e * e = ((f * (c₀ * c₀)) * (f * (c₀ * c₀)))⁻¹ :=
      eq_inv_of_mul_eq_one_left hee_gg
    rw [hee]
    exact hgl.inv_left
  exact hee_l

end CFSG.LocalAnalysis.WeakClosure81

end
