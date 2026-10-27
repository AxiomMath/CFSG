module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCase1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocTab
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCount
public import CFSG.Sporadic.J4.QT2LocUniq

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2


theorem case2_key
    (hF : J4Facts) {A : Subgroup J} (hAP : A ≤ P0) (hn : ∀ g ∈ P0, ∀ x ∈ A, g * x * g⁻¹ ∈ A)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1)
    (hAE : ¬ A ≤ Eg uJ 11) {B : List ℕ} (hBs : B ∈ subs) (hB : MaskList (A ⊓ Eg uJ 11) B)
    {m : J} (hm : m ∈ Subgroup.normalizer (A : Set J)) (hmH : m ∉ Hj) :
    8 * xcnt B = B.length ∧ (∀ w ∈ V0L, w ∈ B) ∧ ∀ x, x ∈ Ig m ↔ x ∈ V0 := by
  classical
  have hM := hF.mat
  have hCE : A ⊓ Eg uJ 11 ≤ Eg uJ 11 := inf_le_right
  have hCA : A ⊓ Eg uJ 11 ≤ A := inf_le_left
  have hnd : B.Nodup := nodup_of_pairwise_lt (subs_prop hBs).2.1
  have hcardC : Nat.card ↥(A ⊓ Eg uJ 11) = B.length := MaskList.card hM hCE hB hnd
  have h16 : 16 ≤ B.length := card_C_ge hF hAP hn hBs hB hAE
  have hidx : (Eg uJ 11).relIndex A ≤ xcnt B := relIndex_le_xcnt hF hAP hn hcomm hsq hB
  have hAcard : Nat.card A = (Eg uJ 11).relIndex A * Nat.card ↥(A ⊓ Eg uJ 11) := by
    have := Subgroup.relIndex_mul_card (H := Eg uJ 11) (K := A)
    rw [inf_comm] at this
    exact this.symm
  obtain ⟨hxb1, hxb2⟩ := x_bound hBs h16
  have hY : cmp m (A ⊓ Eg uJ 11) ≤ A := by
    intro y hy
    have h1 : m⁻¹ * y * m ∈ A := hCA hy
    have := (Subgroup.mem_normalizer_iff.1 hm _).1 h1
    have e : m * (m⁻¹ * y * m) * m⁻¹ = y := by group
    rwa [e] at this
  have hprod := card_mul_card_le hCA hY
  rw [card_cmp, hAcard] at hprod
  have hGsub : ((A ⊓ Eg uJ 11 ⊓ cmp m (A ⊓ Eg uJ 11) : Subgroup J) : Set J) ⊆ Ig m :=
    fun x hx => ⟨hCE hx.1, hCE hx.2⟩
  have hGle : Nat.card ↥(A ⊓ Eg uJ 11 ⊓ cmp m (A ⊓ Eg uJ 11)) ≤ 8 := by
    have h1 := card_inter_le hF hmH
    have h2 := Set.ncard_le_ncard hGsub (Set.toFinite _)
    have h3 : Nat.card ↥(A ⊓ Eg uJ 11 ⊓ cmp m (A ⊓ Eg uJ 11)) =
        ((A ⊓ Eg uJ 11 ⊓ cmp m (A ⊓ Eg uJ 11) : Subgroup J) : Set J).ncard :=
      Nat.card_coe_set_eq _
    rw [h3]
    exact h2.trans h1
  generalize hg : Nat.card ↥(A ⊓ Eg uJ 11 ⊓ cmp m (A ⊓ Eg uJ 11)) = g at hprod hGle
  generalize hi : (Eg uJ 11).relIndex A = i at hprod hidx
  rw [hcardC] at hprod
  have hc0 : 0 < B.length := by omega
  have h1 : B.length ≤ i * g := by
    have : B.length * B.length ≤ (i * g) * B.length := by
      calc B.length * B.length ≤ i * B.length * g := hprod
        _ = (i * g) * B.length := by ring
    exact Nat.le_of_mul_le_mul_right this hc0
  have h2 : i * g ≤ xcnt B * 8 := Nat.mul_le_mul hidx hGle
  have hc8 : 8 * xcnt B = B.length := by omega
  have hxpos : 0 < xcnt B := by omega
  have hg8 : g = 8 := by
    have h3 : xcnt B * 8 ≤ xcnt B * g := by
      calc xcnt B * 8 = B.length := by omega
        _ ≤ i * g := h1
        _ ≤ xcnt B * g := Nat.mul_le_mul_right g hidx
    have := Nat.le_of_mul_le_mul_left h3 hxpos
    omega
  subst hg8
  rcases inter_trio hF hmH with hle | ⟨W, hW, hWc⟩
  · exfalso
    have h4 := (Set.ncard_le_ncard hGsub (Set.toFinite _)).trans hle
    have h3 : Nat.card ↥(A ⊓ Eg uJ 11 ⊓ cmp m (A ⊓ Eg uJ 11)) =
        ((A ⊓ Eg uJ 11 ⊓ cmp m (A ⊓ Eg uJ 11) : Subgroup J) : Set J).ncard :=
      Nat.card_coe_set_eq _
    omega
  · set G : Subgroup J := A ⊓ Eg uJ 11 ⊓ cmp m (A ⊓ Eg uJ 11) with hGdef
    have hGE : G ≤ Eg uJ 11 := inf_le_left.trans hCE
    let BG : List ℕ := (List.range 2048).filter fun c => eta uJ 11 c ∈ G
    have hBG : MaskList G BG := by
      intro c
      simp only [BG, List.mem_filter, List.mem_range, decide_eq_true_eq]
    have hBGnd : BG.Nodup := List.nodup_range.filter _
    have hBGlen : BG.length = 8 := by
      rw [← MaskList.card hM hGE hBG hBGnd]
      exact hg
    have hBGW : ∀ b ∈ BG, b ∈ W := fun b hb => by
      obtain ⟨hlt, hbG⟩ := (hBG b).1 hb
      exact (hWc b hlt).1 (hGsub hbG)
    obtain ⟨hWlen, hWlt, hWnd, -⟩ := trio_prop.2 W hW
    have hsubF : BG.toFinset ⊆ W.toFinset := fun b hb =>
      List.mem_toFinset.2 (hBGW b (List.mem_toFinset.1 hb))
    have hEq : BG.toFinset = W.toFinset := Finset.eq_of_subset_of_card_le hsubF (by
      rw [List.toFinset_card_of_nodup hWnd, List.toFinset_card_of_nodup hBGnd, hWlen, hBGlen])
    have hWB : ∀ w ∈ W, w ∈ B := by
      intro w hw
      have : w ∈ BG.toFinset := by
        rw [hEq]
        exact List.mem_toFinset.2 hw
      obtain ⟨hlt, hwG⟩ := (hBG w).1 (List.mem_toFinset.1 this)
      exact (hB w).2 ⟨hlt, hwG.1⟩
    have hWV : W = V0L := hxb2 hc8 W hW hWB
    subst hWV
    refine ⟨hc8, hWB, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hx.1
      exact (mem_V0_iff hM).2 ⟨c, (hWc c hc).1 hx, rfl⟩
    · obtain ⟨c, hc, rfl⟩ := (mem_V0_iff hM).1 hx
      exact (hWc c (V0L_lt hc)).2 hc

theorem case2
    (hF : J4Facts) {A : Subgroup J} (hAP : A ≤ P0) (hn : ∀ g ∈ P0, ∀ x ∈ A, g * x * g⁻¹ ∈ A)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1)
    (hAE : ¬ A ≤ Eg uJ 11) :
    Subgroup.normalizer (A : Set J) ≤ Hj ∨
      Subgroup.normalizer (A : Set J) ≤ Subgroup.centralizer ({z0} : Set J) ∨
      Subgroup.normalizer (A : Set J) ≤ Subgroup.normalizer (V0 : Set J) := by
  have hM := hF.mat
  have hnC : ∀ g ∈ P0, ∀ x ∈ A ⊓ Eg uJ 11, g * x * g⁻¹ ∈ A ⊓ Eg uJ 11 := fun g hg x hx =>
    ⟨hn g hg x hx.1, Hj_normalizes_Eg hM g (P0_le_Hj hg) x hx.2⟩
  obtain ⟨B, hBs, hB⟩ := subs_complete hF (inf_le_right : A ⊓ Eg uJ 11 ≤ Eg uJ 11) hnC
  by_cases hex : ∃ n ∈ Subgroup.normalizer (A : Set J), n ∉ Hj
  · right; right
    obtain ⟨n0, hn0, hn0H⟩ := hex
    obtain ⟨hc8, hV0B, -⟩ := case2_key hF hAP hn hcomm hsq hAE hBs hB hn0 hn0H
    have h16 : 16 ≤ B.length := card_C_ge hF hAP hn hBs hB hAE
    obtain ⟨-, hxb2⟩ := x_bound hBs h16
    have hIg : ∀ n ∈ Subgroup.normalizer (A : Set J), n ∉ Hj → ∀ x, x ∈ Ig n ↔ x ∈ V0 :=
      fun n hn' hnH => (case2_key hF hAP hn hcomm hsq hAE hBs hB hn' hnH).2.2
    have h2 : ∀ n ∈ Subgroup.normalizer (A : Set J), n ∈ Hj → ∀ x ∈ V0, n * x * n⁻¹ ∈ V0 := by
      intro n hn' hnH x hx
      obtain ⟨c, hc, rfl⟩ := (mem_V0_iff hM).1 hx
      obtain ⟨W', hW'trio, hImg⟩ := (trio_conj hM hnH).1 V0L trio_prop.1
      have hW'B : ∀ w ∈ W', w ∈ B := by
        intro w hw
        obtain ⟨c0, hc0, hc0e⟩ := hImg.2 w hw
        have hc0C : eta uJ 11 c0 ∈ A ⊓ Eg uJ 11 := ((hB c0).1 (hV0B c0 hc0)).2
        have hconj : n * eta uJ 11 c0 * n⁻¹ ∈ A ⊓ Eg uJ 11 :=
          ⟨(Subgroup.mem_normalizer_iff.1 hn' _).1 hc0C.1,
            Hj_normalizes_Eg hM n hnH _ hc0C.2⟩
        rw [hc0e] at hconj
        exact (hB w).2 ⟨(trio_prop.2 W' hW'trio).2.1 w hw, hconj⟩
      have hW' : W' = V0L := hxb2 hc8 W' hW'trio hW'B
      subst hW'
      obtain ⟨c', hc', hc'e⟩ := hImg.1 c hc
      exact (mem_V0_iff hM).2 ⟨c', hc', hc'e⟩
    exact normalizer_V0_of hM hIg h2
  · left
    intro n hn'
    by_contra hnH
    exact hex ⟨n, hn', hnH⟩

end CFSG.Quasithin.J4Loc
