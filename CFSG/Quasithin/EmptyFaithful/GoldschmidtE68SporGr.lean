module

public import Certificates.Data.E68Spor.Gr
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore

public section

namespace CFSG.Quasithin.E6.Spor

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

@[expose] def GrValid (n : ℕ) (L : List ℕ) : Prop := L.Pairwise (· ≤ ·) ∧ ∀ c ∈ L, c < n * n

@[expose] def grLab (n : ℕ) : LabAct (List ℕ) := ⟨grAct n⟩

theorem grAct_tab (g : Γ) (L : List ℕ) :
    grAct n (tab n g).toArray L =
      sortN (L.map fun c => act n g (c / n) * n + act n g (c % n)) := by
  unfold grAct
  congr 1
  apply List.map_congr_left
  intro c _
  change img (tab n g).toArray (c / n) * n + img (tab n g).toArray (c % n) = _
  rw [img_tab, img_tab]

theorem code_div {a b : ℕ} (hb : b < n) : (a * n + b) / n = a := by
  have hn : 0 < n := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, Nat.zero_add]

theorem code_mod {a b : ℕ} (hb : b < n) : (a * n + b) % n = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

theorem code_lt {c : ℕ} (hc : c < n * n) : c / n < n ∧ c % n < n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; omega
    · exact h
  exact ⟨Nat.div_lt_of_lt_mul hc, Nat.mod_lt _ hn⟩

theorem grLab_lawful : LabLawful Γ n (grLab n) (GrValid n) where
  valid_act g L hL := by
    refine ⟨sortN_sorted _, fun c hc => ?_⟩
    have hc' : c ∈ grAct n (tab n g).toArray L := hc
    rw [grAct_tab, mem_sortN] at hc'
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc'
    obtain ⟨h1, h2⟩ := code_lt (hL.2 c0 hc0)
    have h3 := act_lt g h1
    have h4 := act_lt g h2
    nlinarith
  act_mul g h L hL := by
    show grAct n (tab n (g * h)).toArray L =
      grAct n (tab n g).toArray (grAct n (tab n h).toArray L)
    rw [grAct_tab, grAct_tab, grAct_tab, sortN_map_sortN, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    obtain ⟨h1, h2⟩ := code_lt (hL.2 c hc)
    have h4 := act_lt h h2
    simp only [Function.comp]
    rw [code_div h4, code_mod h4, act_mul g h h1, act_mul g h h2]
  act_one {L} hL := by
    show grAct n (tab n (1 : Γ)).toArray L = L
    rw [grAct_tab]
    have : (L.map fun c => act n (1 : Γ) (c / n) * n + act n (1 : Γ) (c % n)) = L := by
      refine (List.map_congr_left (g := fun c => c) fun c hc => ?_).trans (List.map_id' L)
      obtain ⟨h1, h2⟩ := code_lt (hL.2 c hc)
      show act n (1 : Γ) (c / n) * n + act n (1 : Γ) (c % n) = c
      rw [act_one h1, act_one h2]
      exact Nat.div_add_mod' c n
    rw [this]
    exact sortN_of_pairwise hL.1

theorem perm_range_map_act (g : Γ) : List.Perm ((List.range n).map (act n g)) (List.range n) := by
  rw [List.perm_ext_iff_of_nodup]
  · intro a
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact act_lt g hp
    · intro ha
      refine ⟨act n g⁻¹ a, act_lt g⁻¹ ha, ?_⟩
      rw [← act_mul g g⁻¹ ha, mul_inv_cancel, act_one ha]
  · refine List.Nodup.map_on (fun x hx y hy hxy => ?_) (List.nodup_range)
    have hx' := List.mem_range.mp hx
    have hy' := List.mem_range.mp hy
    have h1 : act n g⁻¹ (act n g x) = x := by
      rw [← act_mul g⁻¹ g hx', inv_mul_cancel, act_one hx']
    have h2 : act n g⁻¹ (act n g y) = y := by
      rw [← act_mul g⁻¹ g hy', inv_mul_cancel, act_one hy']
    rw [← h1, ← h2, hxy]
  · exact List.nodup_range

theorem grLabel_eq (z : Γ) :
    grLabel n (tab n z).toArray = (List.range n).map fun p => p * n + act n z p := by
  unfold grLabel
  apply List.map_congr_left
  intro p _
  change p * n + img (tab n z).toArray p = _
  rw [img_tab]

theorem grLabel_valid (z : Γ) : GrValid n (grLabel n (tab n z).toArray) := by
  rw [grLabel_eq]
  refine ⟨?_, fun c hc => ?_⟩
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {p q} hp hq hpq => ?_) List.pairwise_lt_range
    have h1 := act_lt z (List.mem_range.mp hp)
    have h2 : (p + 1) * n ≤ q * n := Nat.mul_le_mul_right n hpq
    nlinarith
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    have h1 := act_lt z (List.mem_range.mp hp)
    have h2 := List.mem_range.mp hp
    have h3 : (p + 1) * n ≤ n * n := Nat.mul_le_mul_right n h2
    nlinarith

theorem lab_graph_of_commute {z g : Γ} (h : g * z = z * g) :
    lab n (grLab n) (grLabel n (tab n z).toArray) g = grLabel n (tab n z).toArray := by
  show grAct n (tab n g).toArray (grLabel n (tab n z).toArray) = grLabel n (tab n z).toArray
  rw [grAct_tab, grLabel_eq, List.map_map]
  have h1 : (List.range n).map
      ((fun c => act n g (c / n) * n + act n g (c % n)) ∘ fun p => p * n + act n z p) =
      (List.range n).map ((fun q => q * n + act n z q) ∘ act n g) := by
    apply List.map_congr_left
    intro p hp
    have hp' := List.mem_range.mp hp
    have hz := act_lt z hp'
    simp only [Function.comp]
    rw [code_div hz, code_mod hz, ← act_mul g z hp', h, act_mul z g hp']
  rw [h1, ← List.map_map]
  have h2 : sortN (((List.range n).map (act n g)).map fun q => q * n + act n z q) =
      sortN ((List.range n).map fun q => q * n + act n z q) :=
    sortN_eq_of_perm ((perm_range_map_act (n := n) g).map _)
  rw [h2]
  exact sortN_of_pairwise (grLabel_eq (n := n) z ▸ (grLabel_valid (n := n) z).1)

theorem card_centralizer_mul_le [Finite Γ] {a b z : Γ}
    (hgen : Subgroup.closure ({a, b} : Set Γ) = ⊤) {zT : Array ℕ}
    (hzT : (tab n z).toArray = zT) {O : OmegaData (List ℕ)}
    (hO : OmegaSpec (grAct n) #[(tab n a).toArray, (tab n b).toArray] (grLabel n zT) O) :
    Nat.card (Subgroup.centralizer ({z} : Set Γ)) * O.lbl.size ≤ Nat.card Γ := by
  subst hzT
  have hel : ∀ l < (#[(tab n a).toArray, (tab n b).toArray] : Array (Array ℕ)).size,
      (#[(tab n a).toArray, (tab n b).toArray] : Array (Array ℕ))[l]! =
        (tab n ((#[a, b] : Array Γ).getD l 1)).toArray := by
    intro l hl
    have hl2 : l < 2 := hl
    interval_cases l <;> rfl
  have hH : Subgroup.closure {x | x ∈ (#[a, b] : Array Γ).toList} = ⊤ := by
    have : {x | x ∈ (#[a, b] : Array Γ).toList} = ({a, b} : Set Γ) := by
      ext x
      simp
    rw [this]
    exact hgen
  have hcard := OmegaSpec.card_top (grLab_lawful (Γ := Γ) (n := n)) (grLabel_valid (n := n) z)
    #[a, b] rfl hel hO hH
  have hle : Subgroup.centralizer ({z} : Set Γ) ≤
      stab (grLab_lawful (Γ := Γ) (n := n)) (grLabel_valid (n := n) z) := fun g hg =>
    lab_graph_of_commute (Subgroup.mem_centralizer_singleton_iff.mp hg)
  calc Nat.card (Subgroup.centralizer ({z} : Set Γ)) * O.lbl.size
      ≤ Nat.card (stab (grLab_lawful (Γ := Γ) (n := n)) (grLabel_valid (n := n) z)) * O.lbl.size :=
        Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hle)
    _ = Nat.card Γ := by rw [hcard, mul_comm]

end CFSG.Quasithin.E6.Spor
