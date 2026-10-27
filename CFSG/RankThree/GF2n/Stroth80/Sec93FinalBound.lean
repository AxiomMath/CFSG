module

public import CFSG.RankThree.GF2n.Stroth80.Sec93FinalStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

@[expose] def ListMaxElemAbStatement : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (T E : Subgroup Y), T ≠ ⊥ → CorBHyp T →
    ListGroup ↥(Subgroup.normalClosure (T : Set Y)) → IsElemAbelian 2 E → T ≤ E →
    E ≤ Subgroup.normalClosure (T : Set Y) → E = T

@[expose] def ListOutRankStatement : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (S L : Subgroup Y), S.Normal → ListGroup ↥S →
    IsElemAbelian 2 L →
    Nat.card L ≤ 4 * Nat.card ↥(L ⊓ (S ⊔ Subgroup.centralizer (S : Set Y)))

theorem sec93f_isElemAbelian_of_le {Y : Type} [Group Y] {E F : Subgroup Y} (h : E ≤ F)
    (hF : IsElemAbelian 2 F) : IsElemAbelian 2 E := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hF.2 x (h hx)⟩
  have h2 := congrArg (fun z : ↥F => (z : Y)) (hF.1.is_comm.comm ⟨a, h a.2⟩ ⟨b, h b.2⟩)
  exact Subtype.ext h2

theorem listWCBound_of_parts (hmax : ListMaxElemAbStatement) (hout : ListOutRankStatement)
    (hsimple : ∀ (D : Type) [Group D] [Finite D], ListGroup D → IsSimpleGroup D)
    (hnc : ∀ (D : Type) [Group D] [Finite D], ListGroup D → ∃ a b : D, a * b ≠ b * a) :
    ListWCBoundStatement := by
  intro Y _ _ T L hT0 hTL hLel hCor hList hclaim
  set S : Subgroup Y := Subgroup.normalClosure (T : Set Y) with hS
  haveI hSn : S.Normal := Subgroup.normalClosure_normal
  set C : Subgroup Y := Subgroup.centralizer (S : Set Y) with hC
  have hTS : T ≤ S := Subgroup.le_normalClosure
  have hTel : IsElemAbelian 2 T := hCor.1
  haveI hsimp : IsSimpleGroup ↥S := hsimple _ hList
  obtain ⟨a, b, hab⟩ := hnc _ hList
  have hSC : S ⊓ C = ⊥ := by
    have hcen : Subgroup.center ↥S = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥S) with h | h
      · exact h
      · exfalso
        apply hab
        have := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b
        exact this.symm
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxc : (⟨x, hxS⟩ : ↥S) ∈ Subgroup.center ↥S :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
    rw [hcen, Subgroup.mem_bot] at hxc
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxc
  have hnotN : ¬ S ≤ Subgroup.normalizer (T : Set Y) := by
    intro hN
    have hNg : ∀ g : Y, S ≤ Subgroup.normalizer (conjSubgroup g T : Set Y) := by
      intro g s hs
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hgs : g⁻¹ * s * g ∈ S := by
        have := hSn.conj_mem s hs g⁻¹
        simpa using this
      have hn := Subgroup.mem_normalizer_iff.mp (hN hgs) (g⁻¹ * y * g)
      rw [mem_conjSubgroup, mem_conjSubgroup]
      have e : g⁻¹ * (s * y * s⁻¹) * g = (g⁻¹ * s * g) * (g⁻¹ * y * g) * (g⁻¹ * s * g)⁻¹ := by
        group
      rw [e]
      exact hn
    have hTg : ∀ g : Y, conjSubgroup g T = T := by
      intro g
      have hgS : conjSubgroup g T ≤ S := by
        intro y hy
        obtain ⟨t, ht, rfl⟩ := hy
        exact hSn.conj_mem t (hTS ht) g
      rcases hCor.2.1 g with h0 | h1
      · refine (hCor.2.2 g).mp fun x hx y hy => ?_
        have hxS : x ∈ S := hTS hx
        have hyS : y ∈ S := hgS hy
        have h1 : x * y * x⁻¹ * y⁻¹ ∈ conjSubgroup g T := by
          have h2 := (Subgroup.mem_normalizer_iff.mp (hNg g hxS) y).mp hy
          exact (conjSubgroup g T).mul_mem h2 ((conjSubgroup g T).inv_mem hy)
        have h3 : x * y * x⁻¹ * y⁻¹ ∈ T := by
          have h4 := (Subgroup.mem_normalizer_iff.mp (hN hyS) x⁻¹).mp (T.inv_mem hx)
          have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
          rw [e]
          exact T.mul_mem hx h4
        have h5 : x * y * x⁻¹ * y⁻¹ ∈ T ⊓ conjSubgroup g T := ⟨h3, h1⟩
        rw [h0, Subgroup.mem_bot] at h5
        have h6 : x * y = y * x := by
          have := congrArg (· * (y * x)) h5
          simp only [one_mul] at this
          calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
            _ = y * x := by rw [h5, one_mul]
        exact h6
      · have hle : T ≤ conjSubgroup g T := inf_eq_left.mp h1
        exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])).symm
    have hTnorm : T.Normal := ⟨fun t ht g => by
      have : g * t * g⁻¹ ∈ conjSubgroup g T := ⟨t, ht, rfl⟩
      rwa [hTg g] at this⟩
    have hST : S = T := Subgroup.normalClosure_eq_self T
    apply hab
    have ha : (a : Y) ∈ T := hST ▸ a.2
    have hb : (b : Y) ∈ T := hST ▸ b.2
    have h2 := congrArg (fun z : ↥T => (z : Y)) (hTel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    exact Subtype.ext h2
  have hLS : L ⊓ S = T :=
    hmax Y T (L ⊓ S) hT0 hCor hList (sec93f_isElemAbelian_of_le inf_le_left hLel)
      (le_inf hTL hTS) inf_le_right
  have hLC : L ⊓ C = ⊥ := by
    by_contra hne
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
    apply hnotN
    intro h hhS
    have hxh : x ∈ conjSubgroup h L := by
      rw [mem_conjSubgroup]
      have hc : h⁻¹ * x * h = x := by
        have := Subgroup.mem_centralizer_iff.mp hxC h⁻¹ (S.inv_mem hhS)
        calc h⁻¹ * x * h = x * h⁻¹ * h := by rw [this]
          _ = x := by group
      rw [hc]
      exact hxL
    have hne2 : L ⊓ conjSubgroup h L ≠ ⊥ := by
      intro h0
      have hmem : x ∈ L ⊓ conjSubgroup h L := ⟨hxL, hxh⟩
      rw [h0, Subgroup.mem_bot] at hmem
      exact hx1 (Subtype.ext hmem)
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hclaim h hne2)
    obtain ⟨huT, huL⟩ := Subgroup.mem_inf.mp hu
    have hhu : h⁻¹ * u * h ∈ L := mem_conjSubgroup.mp huL
    have hhuS : h⁻¹ * u * h ∈ S := by
      have := hSn.conj_mem u (hTS huT) h⁻¹
      simpa using this
    have hhuT : h⁻¹ * u * h ∈ T := by
      rw [← hLS]
      exact ⟨hhu, hhuS⟩
    have hmemT : u ∈ conjSubgroup h T := mem_conjSubgroup.mpr hhuT
    have hu1' : u ≠ 1 := fun h' => hu1 (Subtype.ext h')
    have hTI : T ⊓ conjSubgroup h T = T := by
      rcases hCor.2.1 h with h0 | h1
      · exfalso
        have : u ∈ T ⊓ conjSubgroup h T := ⟨huT, hmemT⟩
        rw [h0, Subgroup.mem_bot] at this
        exact hu1' this
      · exact h1
    have hle : T ≤ conjSubgroup h T := inf_eq_left.mp hTI
    have heq : conjSubgroup h T = T :=
      (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])).symm
    exact conjSubgroup_eq_self_iff.mp heq
  have hcomm : ∀ s ∈ S, ∀ c ∈ C, c * s = s * c := fun s hs c hc =>
    (Subgroup.mem_centralizer_iff.mp hc s hs).symm
  let E₀ : Subgroup Y :=
    { carrier := {s | s ∈ S ∧ ∃ c ∈ C, s * c ∈ L}
      mul_mem' := by
        rintro s s' ⟨hs, c, hc, hsc⟩ ⟨hs', c', hc', hsc'⟩
        refine ⟨S.mul_mem hs hs', c * c', C.mul_mem hc hc', ?_⟩
        have e : s * s' * (c * c') = (s * c) * (s' * c') := by
          calc s * s' * (c * c') = s * (s' * c) * c' := by group
            _ = s * (c * s') * c' := by rw [hcomm s' hs' c hc]
            _ = (s * c) * (s' * c') := by group
        rw [e]
        exact L.mul_mem hsc hsc'
      one_mem' := ⟨S.one_mem, 1, C.one_mem, by simpa using L.one_mem⟩
      inv_mem' := by
        rintro s ⟨hs, c, hc, hsc⟩
        refine ⟨S.inv_mem hs, c⁻¹, C.inv_mem hc, ?_⟩
        have e : s⁻¹ * c⁻¹ = (s * c)⁻¹ := by
          calc s⁻¹ * c⁻¹ = c⁻¹ * s⁻¹ := by
                have := hcomm s⁻¹ (S.inv_mem hs) c⁻¹ (C.inv_mem hc)
                exact this.symm
            _ = (s * c)⁻¹ := by group
        rw [e]
        exact L.inv_mem hsc }
  have hmemE : ∀ s, s ∈ E₀ ↔ s ∈ S ∧ ∃ c ∈ C, s * c ∈ L := fun s => Iff.rfl
  have hE₀el : IsElemAbelian 2 E₀ := by
    have hsq : ∀ s ∈ E₀, s * s = 1 := by
      rintro s hs
      obtain ⟨hsS, c, hc, hsc⟩ := (hmemE s).mp hs
      have h2 := hLel.2 (s * c) hsc
      rw [pow_two] at h2
      have hcs : c * s = s * c := hcomm s hsS c hc
      have h3 : s * s * (c * c) = 1 := by
        calc s * s * (c * c) = s * (s * c) * c := by group
          _ = s * (c * s) * c := by rw [hcs]
          _ = s * c * (s * c) := by group
          _ = 1 := h2
      have h4 : s * s = (c * c)⁻¹ := eq_inv_of_mul_eq_one_left h3
      have h5 : s * s ∈ S ⊓ C := ⟨S.mul_mem hsS hsS, by rw [h4]; exact C.inv_mem (C.mul_mem hc hc)⟩
      rw [hSC, Subgroup.mem_bot] at h5
      exact h5
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨x, hxE⟩ := x
      obtain ⟨y, hyE⟩ := y
      obtain ⟨hxS, c, hc, hxc⟩ := (hmemE x).mp hxE
      obtain ⟨hyS, c', hc', hyc'⟩ := (hmemE y).mp hyE
      have hcomm1 := hLel.1.is_comm.comm ⟨_, hxc⟩ ⟨_, hyc'⟩
      have hxy : x * c * (y * c') = y * c' * (x * c) := congrArg Subtype.val hcomm1
      have e1 : x * y * (c * c') = y * x * (c' * c) := by
        calc x * y * (c * c') = x * (y * c) * c' := by group
          _ = x * (c * y) * c' := by rw [hcomm y hyS c hc]
          _ = x * c * (y * c') := by group
          _ = y * c' * (x * c) := hxy
          _ = y * (c' * x) * c := by group
          _ = y * (x * c') * c := by rw [hcomm x hxS c' hc']
          _ = y * x * (c' * c) := by group
      have e2 : (y * x)⁻¹ * (x * y) = c' * c * (c * c')⁻¹ := by
        calc (y * x)⁻¹ * (x * y) = (y * x)⁻¹ * ((x * y) * (c * c') * (c * c')⁻¹) := by group
          _ = (y * x)⁻¹ * ((y * x) * (c' * c) * (c * c')⁻¹) := by rw [e1]
          _ = c' * c * (c * c')⁻¹ := by group
      have e3 : (y * x)⁻¹ * (x * y) ∈ S ⊓ C := by
        refine ⟨S.mul_mem (S.inv_mem (S.mul_mem hyS hxS)) (S.mul_mem hxS hyS), ?_⟩
        rw [e2]
        exact C.mul_mem (C.mul_mem hc' hc) (C.inv_mem (C.mul_mem hc hc'))
      rw [hSC, Subgroup.mem_bot] at e3
      refine Subtype.ext ?_
      show x * y = y * x
      have h6 : x * y = y * x := by
        calc x * y = (y * x) * ((y * x)⁻¹ * (x * y)) := by group
          _ = y * x := by rw [e3, mul_one]
      exact h6
    · rw [pow_two]
      exact hsq x hx
  have hTE : T ≤ E₀ := fun t ht => (hmemE t).mpr ⟨hTS ht, 1, C.one_mem, by simpa using hTL ht⟩
  have hE₀S : E₀ ≤ S := fun s hs => ((hmemE s).mp hs).1
  have hE₀T : E₀ = T := hmax Y T E₀ hT0 hCor hList hE₀el hTE hE₀S
  have hL0 : L ⊓ (S ⊔ C) = T := by
    refine le_antisymm (fun x hx => ?_) (le_inf hTL (hTS.trans le_sup_left))
    obtain ⟨hxL, hxSC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨s, hsS, c, hcC, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxSC
    have hsE : s ∈ E₀ := (hmemE s).mpr ⟨hsS, c, hcC, hxL⟩
    have hsT : s ∈ T := hE₀T ▸ hsE
    have hcL : c ∈ L := by
      have := L.mul_mem (L.inv_mem (hTL hsT)) hxL
      simpa using this
    have hc1 : c ∈ L ⊓ C := ⟨hcL, hcC⟩
    rw [hLC, Subgroup.mem_bot] at hc1
    rw [hc1, mul_one]
    exact hsT
  have hbd := hout Y S L hSn hList hLel
  rw [hL0] at hbd
  have hT2 : 1 < Nat.card T := (Subgroup.one_lt_card_iff_ne_bot T).mpr hT0
  have h8 : 8 ≤ Nat.card T ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ Nat.card T ^ 3 := Nat.pow_le_pow_left hT2 3
  have h4 : Nat.card T ^ 4 = Nat.card T * Nat.card T ^ 3 := by ring
  rw [h4]
  nlinarith

end CFSG.RankThree.GF2n.Stroth80
