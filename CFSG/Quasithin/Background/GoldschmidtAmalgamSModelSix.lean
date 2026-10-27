module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSTypeB
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSTwoLocal
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSSixCoatom
import CFSG.Quasithin.Background.GoldschmidtAmalgamSModelSixPack

public section

set_option synthInstance.maxSize 2000

namespace CFSG.Quasithin.F6.GoldAmS

open Equiv CFSG.Open CFSG.Permutation.FinPack CFSG.Quasithin.F6.GoldAmS.Pack

abbrev S6 := Perm (Fin 6)

@[expose] def s6e1 : S6 := swap 4 5

@[expose] def s6e2 : S6 := swap 0 1 * swap 2 3 * swap 4 5

def S6G1 : Subgroup S6 := Subgroup.centralizer ({s6e1} : Set S6)

def S6G2 : Subgroup S6 := Subgroup.centralizer ({s6e2} : Set S6)

def S6K1 : Subgroup S6 := S6G1 ⊓ alternatingGroup (Fin 6)

def S6K2 : Subgroup S6 := S6G2 ⊓ alternatingGroup (Fin 6)

theorem mem_S6G1 {g : S6} : g ∈ S6G1 ↔ g * s6e1 = s6e1 * g := by
  rw [S6G1, Subgroup.mem_centralizer_singleton_iff]

theorem mem_S6G2 {g : S6} : g ∈ S6G2 ↔ g * s6e2 = s6e2 * g := by
  rw [S6G2, Subgroup.mem_centralizer_singleton_iff]

theorem mem_S6K1 {g : S6} : g ∈ S6K1 ↔ g * s6e1 = s6e1 * g ∧ Equiv.Perm.sign g = 1 := by
  rw [S6K1, Subgroup.mem_inf, mem_S6G1, Equiv.Perm.mem_alternatingGroup]

theorem mem_S6K2 {g : S6} : g ∈ S6K2 ↔ g * s6e2 = s6e2 * g ∧ Equiv.Perm.sign g = 1 := by
  rw [S6K2, Subgroup.mem_inf, mem_S6G2, Equiv.Perm.mem_alternatingGroup]

instance : DecidablePred (· ∈ S6G1) := fun _ => decidable_of_iff _ mem_S6G1.symm
instance : DecidablePred (· ∈ S6G2) := fun _ => decidable_of_iff _ mem_S6G2.symm
instance : DecidablePred (· ∈ S6K1) := fun _ => decidable_of_iff _ mem_S6K1.symm
instance : DecidablePred (· ∈ S6K2) := fun _ => decidable_of_iff _ mem_S6K2.symm
instance : DecidablePred (· ∈ S6G1 ⊓ S6G2) := fun g =>
  inferInstanceAs (Decidable (g ∈ S6G1 ∧ g ∈ S6G2))
instance : DecidablePred (· ∈ S6K1 ⊓ S6K2) := fun g =>
  inferInstanceAs (Decidable (g ∈ S6K1 ∧ g ∈ S6K2))

theorem card_S6 : Nat.card S6 = 720 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  simp [Nat.factorial]

theorem card_S6G1 : Nat.card S6G1 = 48 := by
  have he1 : enc s6e1 = 4534800 := by decide +kernel
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    card_filter_of_iff (· ∈ S6G1) (gK 4534800) fun g => mem_S6G1.trans (cent_iff he1)]
  decide +kernel

theorem card_S6G2 : Nat.card S6G2 = 48 := by
  have he2 : enc s6e2 = 4530945 := by decide +kernel
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    card_filter_of_iff (· ∈ S6G2) (gK 4530945) fun g => mem_S6G2.trans (cent_iff he2)]
  decide +kernel

theorem card_S6K1 : Nat.card S6K1 = 24 := by
  have he1 : enc s6e1 = 4534800 := by decide +kernel
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    card_filter_of_iff (· ∈ S6K1) k1K fun g => by
      rw [mem_S6K1, cent_iff he1, sign_eq_one_iff_evenK h6, k1K, Bool.and_eq_true]]
  decide +kernel

theorem card_S6K2 : Nat.card S6K2 = 24 := by
  have he2 : enc s6e2 = 4530945 := by decide +kernel
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    card_filter_of_iff (· ∈ S6K2) k2K fun g => by
      rw [mem_S6K2, cent_iff he2, sign_eq_one_iff_evenK h6, k2K, Bool.and_eq_true]]
  decide +kernel

theorem card_S6T : Nat.card ↥(S6G1 ⊓ S6G2) = 16 := by
  have he1 : enc s6e1 = 4534800 := by decide +kernel
  have he2 : enc s6e2 = 4530945 := by decide +kernel
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    card_filter_of_iff (· ∈ S6G1 ⊓ S6G2) tK fun g => by
      rw [Subgroup.mem_inf, mem_S6G1, mem_S6G2, cent_iff he1, cent_iff he2, tK,
        Bool.and_eq_true]]
  decide +kernel

theorem card_S6H : Nat.card ↥(S6K1 ⊓ S6K2) = 8 := by
  have he1 : enc s6e1 = 4534800 := by decide +kernel
  have he2 : enc s6e2 = 4530945 := by decide +kernel
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    card_filter_of_iff (· ∈ S6K1 ⊓ S6K2) hK fun g => by
      rw [Subgroup.mem_inf, mem_S6K1, mem_S6K2, cent_iff he1, cent_iff he2,
        sign_eq_one_iff_evenK h6, hK, k1K, k2K, Bool.and_eq_true, Bool.and_eq_true,
        Bool.and_eq_true]]
  decide +kernel

@[expose] def s6pa : S6 := swap 0 1 * swap 2 3
@[expose] def s6pb : S6 := swap 0 2 * swap 1 3
@[expose] def s6pc : S6 := swap 0 3 * swap 1 2
@[expose] def s6pd : S6 := swap 2 3 * swap 4 5
@[expose] def s6pf : S6 := swap 0 1 * swap 4 5

def S6N1 : Subgroup S6 where
  carrier := {g | g = 1 ∨ g = s6pa ∨ g = s6pb ∨ g = s6pc}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have h : ∀ a : S6, (a = 1 ∨ a = s6pa ∨ a = s6pb ∨ a = s6pc) → ∀ b : S6,
        (b = 1 ∨ b = s6pa ∨ b = s6pb ∨ b = s6pc) → (a * b = 1 ∨ a * b = s6pa ∨ a * b = s6pb ∨
          a * b = s6pc) := by
      have hpa : enc s6pa = 5513985 := by decide +kernel
      have hpb : enc s6pb = 5509170 := by decide +kernel
      have hpc : enc s6pc = 5505315 := by decide +kernel
      intro a ha b hb
      rw [mem4_iff hpa hpb hpc] at ha hb ⊢
      rw [enc_mul h6]
      exact allK_iff.1 (allK_iff.1 n1_mul_ok _ (memK_iff.1 ha)) _ (memK_iff.1 hb)
    exact fun {a b} ha hb => h a ha b hb
  inv_mem' := by
    have h : ∀ a : S6, (a = 1 ∨ a = s6pa ∨ a = s6pb ∨ a = s6pc) →
        (a⁻¹ = 1 ∨ a⁻¹ = s6pa ∨ a⁻¹ = s6pb ∨ a⁻¹ = s6pc) := by
      have hpa : enc s6pa = 5513985 := by decide +kernel
      have hpb : enc s6pb = 5509170 := by decide +kernel
      have hpc : enc s6pc = 5505315 := by decide +kernel
      intro a ha
      rw [mem4_iff hpa hpb hpc] at ha ⊢
      rw [enc_inv_invCK h6]
      exact allK_iff.1 n1_inv_ok _ (memK_iff.1 ha)
    exact fun {a} ha => h a ha

def S6N2 : Subgroup S6 where
  carrier := {g | g = 1 ∨ g = s6pa ∨ g = s6pd ∨ g = s6pf}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have h : ∀ a : S6, (a = 1 ∨ a = s6pa ∨ a = s6pd ∨ a = s6pf) → ∀ b : S6,
        (b = 1 ∨ b = s6pa ∨ b = s6pd ∨ b = s6pf) → (a * b = 1 ∨ a * b = s6pa ∨ a * b = s6pd ∨
          a * b = s6pf) := by
      have hpa : enc s6pa = 5513985 := by decide +kernel
      have hpd : enc s6pd = 4530960 := by decide +kernel
      have hpf : enc s6pf = 4534785 := by decide +kernel
      intro a ha b hb
      rw [mem4_iff hpa hpd hpf] at ha hb ⊢
      rw [enc_mul h6]
      exact allK_iff.1 (allK_iff.1 n2_mul_ok _ (memK_iff.1 ha)) _ (memK_iff.1 hb)
    exact fun {a b} ha hb => h a ha b hb
  inv_mem' := by
    have h : ∀ a : S6, (a = 1 ∨ a = s6pa ∨ a = s6pd ∨ a = s6pf) →
        (a⁻¹ = 1 ∨ a⁻¹ = s6pa ∨ a⁻¹ = s6pd ∨ a⁻¹ = s6pf) := by
      have hpa : enc s6pa = 5513985 := by decide +kernel
      have hpd : enc s6pd = 4530960 := by decide +kernel
      have hpf : enc s6pf = 4534785 := by decide +kernel
      intro a ha
      rw [mem4_iff hpa hpd hpf] at ha ⊢
      rw [enc_inv_invCK h6]
      exact allK_iff.1 n2_inv_ok _ (memK_iff.1 ha)
    exact fun {a} ha => h a ha

instance : DecidablePred (· ∈ S6N1) := fun g =>
  inferInstanceAs (Decidable (g = 1 ∨ g = s6pa ∨ g = s6pb ∨ g = s6pc))
instance : DecidablePred (· ∈ S6N2) := fun g =>
  inferInstanceAs (Decidable (g = 1 ∨ g = s6pa ∨ g = s6pd ∨ g = s6pf))

theorem card_S6N1 : Nat.card S6N1 = 4 := by
  have hpa : enc s6pa = 5513985 := by decide +kernel
  have hpb : enc s6pb = 5509170 := by decide +kernel
  have hpc : enc s6pc = 5505315 := by decide +kernel
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    card_filter_of_iff (· ∈ S6N1) (fun c => memK c [oneS, 5513985, 5509170, 5505315])
      fun g => mem4_iff hpa hpb hpc]
  decide +kernel

theorem card_S6N2 : Nat.card S6N2 = 4 := by
  have hpa : enc s6pa = 5513985 := by decide +kernel
  have hpd : enc s6pd = 4530960 := by decide +kernel
  have hpf : enc s6pf = 4534785 := by decide +kernel
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    card_filter_of_iff (· ∈ S6N2) (fun c => memK c [oneS, 5513985, 4530960, 4534785])
      fun g => mem4_iff hpa hpd hpf]
  decide +kernel

theorem s6_N1_le_K1 : ∀ g : S6, g ∈ S6N1 → g ∈ S6K1 := by
  have hpa : enc s6pa = 5513985 := by decide +kernel
  have hpb : enc s6pb = 5509170 := by decide +kernel
  have hpc : enc s6pc = 5505315 := by decide +kernel
  have he1 : enc s6e1 = 4534800 := by decide +kernel
  intro g hg
  have h := allK_iff.1 n1_ok _ (memK_iff.1 ((mem4_iff hpa hpb hpc).1 hg))
  rw [k1K, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  rw [mem_S6K1, cent_iff he1, sign_eq_one_iff_evenK h6]
  exact h.1.1

theorem s6_N2_le_K2 : ∀ g : S6, g ∈ S6N2 → g ∈ S6K2 := by
  have hpa : enc s6pa = 5513985 := by decide +kernel
  have hpd : enc s6pd = 4530960 := by decide +kernel
  have hpf : enc s6pf = 4534785 := by decide +kernel
  have he2 : enc s6e2 = 4530945 := by decide +kernel
  intro g hg
  have h := allK_iff.1 n2_ok _ (memK_iff.1 ((mem4_iff hpa hpd hpf).1 hg))
  rw [k2K, Bool.and_eq_true, Bool.and_eq_true] at h
  rw [mem_S6K2, cent_iff he2, sign_eq_one_iff_evenK h6]
  exact h.1

theorem s6_N1_le_K2 : ∀ g : S6, g ∈ S6N1 → g ∈ S6K2 := by
  have hpa : enc s6pa = 5513985 := by decide +kernel
  have hpb : enc s6pb = 5509170 := by decide +kernel
  have hpc : enc s6pc = 5505315 := by decide +kernel
  have he2 : enc s6e2 = 4530945 := by decide +kernel
  intro g hg
  have h := allK_iff.1 n1_ok _ (memK_iff.1 ((mem4_iff hpa hpb hpc).1 hg))
  rw [k2K, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  rw [mem_S6K2, cent_iff he2, sign_eq_one_iff_evenK h6]
  exact h.1.2

theorem s6_K1_normalizes_N1 :
    ∀ g : S6, g ∈ S6K1 → ∀ q : S6, q ∈ S6N1 → g * q * g⁻¹ ∈ S6N1 := by
  have hpa : enc s6pa = 5513985 := by decide +kernel
  have hpb : enc s6pb = 5509170 := by decide +kernel
  have hpc : enc s6pc = 5505315 := by decide +kernel
  have he1 : enc s6e1 = 4534800 := by decide +kernel
  intro g hg q hq
  have hk : k1K (enc g) = true := by
    rw [mem_S6K1, cent_iff he1, sign_eq_one_iff_evenK h6] at hg
    rw [k1K, Bool.and_eq_true]
    exact hg
  have h := walkK_sound k1_norm_ok g
  rw [hk, Bool.not_true, Bool.false_or] at h
  have h2 := allK_iff.1 h _ (memK_iff.1 ((mem4_iff hpa hpb hpc).1 hq))
  rw [← enc_conj6] at h2
  exact (mem4_iff hpa hpb hpc).2 h2

theorem s6_K2_normalizes_N2 :
    ∀ g : S6, g ∈ S6K2 → ∀ q : S6, q ∈ S6N2 → g * q * g⁻¹ ∈ S6N2 := by
  have hpa : enc s6pa = 5513985 := by decide +kernel
  have hpd : enc s6pd = 4530960 := by decide +kernel
  have hpf : enc s6pf = 4534785 := by decide +kernel
  have he2 : enc s6e2 = 4530945 := by decide +kernel
  intro g hg q hq
  have hk : k2K (enc g) = true := by
    rw [mem_S6K2, cent_iff he2, sign_eq_one_iff_evenK h6] at hg
    rw [k2K, Bool.and_eq_true]
    exact hg
  have h := walkK_sound k2_norm_ok g
  rw [hk, Bool.not_true, Bool.false_or] at h
  have h2 := allK_iff.1 h _ (memK_iff.1 ((mem4_iff hpa hpd hpf).1 hq))
  rw [← enc_conj6] at h2
  exact (mem4_iff hpa hpd hpf).2 h2

theorem s6_N1_exp : ∀ q : S6, q ∈ S6N1 → q * q = 1 := by
  have hpa : enc s6pa = 5513985 := by decide +kernel
  have hpb : enc s6pb = 5509170 := by decide +kernel
  have hpc : enc s6pc = 5505315 := by decide +kernel
  intro g hg
  have h := allK_iff.1 n1_ok _ (memK_iff.1 ((mem4_iff hpa hpb hpc).1 hg))
  rw [Bool.and_eq_true, ← enc_mul h6, ← enc_oneS, beq_enc_iff h6] at h
  exact h.2

theorem s6_N2_exp : ∀ q : S6, q ∈ S6N2 → q * q = 1 := by
  have hpa : enc s6pa = 5513985 := by decide +kernel
  have hpd : enc s6pd = 4530960 := by decide +kernel
  have hpf : enc s6pf = 4534785 := by decide +kernel
  intro g hg
  have h := allK_iff.1 n2_ok _ (memK_iff.1 ((mem4_iff hpa hpd hpf).1 hg))
  rw [Bool.and_eq_true, ← enc_mul h6, ← enc_oneS, beq_enc_iff h6] at h
  exact h.2

theorem s6_K1_cent :
    ∀ g : S6, g ∈ S6K1 → (∀ q : S6, q ∈ S6N1 → g * q = q * g) → g ∈ S6N1 := by
  have hpa : enc s6pa = 5513985 := by decide +kernel
  have hpb : enc s6pb = 5509170 := by decide +kernel
  have hpc : enc s6pc = 5505315 := by decide +kernel
  have he1 : enc s6e1 = 4534800 := by decide +kernel
  intro g hg hc
  have hk : k1K (enc g) = true := by
    rw [mem_S6K1, cent_iff he1, sign_eq_one_iff_evenK h6] at hg
    rw [k1K, Bool.and_eq_true]
    exact hg
  have hq : allK (fun q => gK q (enc g)) [oneS, 5513985, 5509170, 5505315] = true := by
    refine allK_iff.2 fun x hx => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (cent_iff enc_oneS).1 (hc 1 (Or.inl rfl))
    · exact (cent_iff hpa).1 (hc s6pa (Or.inr (Or.inl rfl)))
    · exact (cent_iff hpb).1 (hc s6pb (Or.inr (Or.inr (Or.inl rfl))))
    · exact (cent_iff hpc).1 (hc s6pc (Or.inr (Or.inr (Or.inr rfl))))
  have h := walkK_sound k1_cent_ok g
  rw [hk, hq] at h
  simp only [Bool.not_true, Bool.false_or] at h
  exact (mem4_iff hpa hpb hpc).2 h

theorem s6_K2_cent :
    ∀ g : S6, g ∈ S6K2 → (∀ q : S6, q ∈ S6N2 → g * q = q * g) → g ∈ S6N2 := by
  have hpa : enc s6pa = 5513985 := by decide +kernel
  have hpd : enc s6pd = 4530960 := by decide +kernel
  have hpf : enc s6pf = 4534785 := by decide +kernel
  have he2 : enc s6e2 = 4530945 := by decide +kernel
  intro g hg hc
  have hk : k2K (enc g) = true := by
    rw [mem_S6K2, cent_iff he2, sign_eq_one_iff_evenK h6] at hg
    rw [k2K, Bool.and_eq_true]
    exact hg
  have hq : allK (fun q => gK q (enc g)) [oneS, 5513985, 4530960, 4534785] = true := by
    refine allK_iff.2 fun x hx => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (cent_iff enc_oneS).1 (hc 1 (Or.inl rfl))
    · exact (cent_iff hpa).1 (hc s6pa (Or.inr (Or.inl rfl)))
    · exact (cent_iff hpd).1 (hc s6pd (Or.inr (Or.inr (Or.inl rfl))))
    · exact (cent_iff hpf).1 (hc s6pf (Or.inr (Or.inr (Or.inr rfl))))
  have h := walkK_sound k2_cent_ok g
  rw [hk, hq] at h
  simp only [Bool.not_true, Bool.false_or] at h
  exact (mem4_iff hpa hpd hpf).2 h

theorem s6_N1_not_N2 : ∃ g : S6, g ∈ S6N1 ∧ g ∉ S6N2 := by
  have hpa : enc s6pa = 5513985 := by decide +kernel
  have hpd : enc s6pd = 4530960 := by decide +kernel
  have hpf : enc s6pf = 4534785 := by decide +kernel
  have hpb : enc s6pb = 5509170 := by decide +kernel
  refine ⟨s6pb, Or.inr (Or.inr (Or.inl rfl)), fun h => ?_⟩
  have h1 := (mem4_iff hpa hpd hpf).1 h
  rw [hpb] at h1
  exact absurd h1 (by decide +kernel)

theorem vertexA_S6K1 : VertexA S6K1 S6N1 where
  le := fun g hg => s6_N1_le_K1 g hg
  normal := fun g hg q hq => s6_K1_normalizes_N1 g hg q hq
  card_A := card_S6K1
  card_Q := card_S6N1
  exp := fun q hq => s6_N1_exp q hq
  cent := fun g hg h => s6_K1_cent g hg fun q hq => h q hq

theorem vertexA_S6K2 : VertexA S6K2 S6N2 where
  le := fun g hg => s6_N2_le_K2 g hg
  normal := fun g hg q hq => s6_K2_normalizes_N2 g hg q hq
  card_A := card_S6K2
  card_Q := card_S6N2
  exp := fun q hq => s6_N2_exp q hq
  cent := fun g hg h => s6_K2_cent g hg fun q hq => h q hq

theorem typeA_S6 : TypeA S6K1 S6K2 := by
  refine ⟨S6N1, S6N2, vertexA_S6K1, vertexA_S6K2, fun g hg => s6_N1_le_K2 g hg, ?_, card_S6H⟩
  intro h
  obtain ⟨g, hg1, hg2⟩ := s6_N1_not_N2
  exact hg2 (h ▸ hg1)

theorem s6e1_mem_G2 : s6e1 ∈ S6G2 := by
  rw [mem_S6G2]; decide

theorem s6e2_mem_G1 : s6e2 ∈ S6G1 := by
  rw [mem_S6G1]; decide

theorem s6z_ne : s6e1 * s6e2 ≠ 1 := by decide

theorem s6z_mem : s6e1 * s6e2 ∈ S6K1 ⊓ S6K2 := by
  show s6e1 * s6e2 ∈ S6K1 ∧ s6e1 * s6e2 ∈ S6K2
  decide

theorem s6_inf_split :
    ∀ t : S6, t ∈ S6G1 ⊓ S6G2 → t ∈ S6K1 ⊓ S6K2 ∨ s6e1 * t ∈ S6K1 ⊓ S6K2 := by
  have he1 : enc s6e1 = 4534800 := by decide +kernel
  have he2 : enc s6e2 = 4530945 := by decide +kernel
  have hH : ∀ g : S6, g ∈ S6K1 ⊓ S6K2 ↔ hK (enc g) = true := fun g => by
    rw [Subgroup.mem_inf, mem_S6K1, mem_S6K2, cent_iff he1, cent_iff he2,
      sign_eq_one_iff_evenK h6, hK, k1K, k2K, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true]
  intro t ht
  rw [Subgroup.mem_inf, mem_S6G1, mem_S6G2, cent_iff he1, cent_iff he2] at ht
  have h := walkK_sound split_ok t
  rw [tK, ht.1, ht.2, Bool.and_true, Bool.not_true, Bool.false_or, ← he1, ← enc_mul h6,
    Bool.or_eq_true, ← hH, ← hH] at h
  exact h

theorem s6_prod₁ : ProdStr S6G1 S6K1 s6e1 where
  le := inf_le_left
  mem := mem_S6G1.2 rfl
  sq := by decide
  central := fun g hg => mem_S6G1.1 hg
  not_mem := by
    have : ¬ (s6e1 ∈ S6K1) := by decide
    exact this
  split := by
    have h : ∀ g : S6, g ∈ S6G1 → g ∈ S6K1 ∨ s6e1 * g ∈ S6K1 := by
      have he1 : enc s6e1 = 4534800 := by decide +kernel
      have hK1 : ∀ g : S6, g ∈ S6K1 ↔ k1K (enc g) = true := fun g => by
        rw [mem_S6K1, cent_iff he1, sign_eq_one_iff_evenK h6, k1K, Bool.and_eq_true]
      intro g hg
      rw [mem_S6G1, cent_iff he1] at hg
      have h := walkK_sound split1_ok g
      rw [hg, Bool.not_true, Bool.false_or, ← he1, ← enc_mul h6, Bool.or_eq_true, ← hK1,
        ← hK1] at h
      exact h
    exact h

theorem s6_prod₂ : ProdStr S6G2 S6K2 s6e2 where
  le := inf_le_left
  mem := mem_S6G2.2 rfl
  sq := by decide
  central := fun g hg => mem_S6G2.1 hg
  not_mem := by
    have : ¬ (s6e2 ∈ S6K2) := by decide
    exact this
  split := by
    have h : ∀ g : S6, g ∈ S6G2 → g ∈ S6K2 ∨ s6e2 * g ∈ S6K2 := by
      have he2 : enc s6e2 = 4530945 := by decide +kernel
      have hK2 : ∀ g : S6, g ∈ S6K2 ↔ k2K (enc g) = true := fun g => by
        rw [mem_S6K2, cent_iff he2, sign_eq_one_iff_evenK h6, k2K, Bool.and_eq_true]
      intro g hg
      rw [mem_S6G2, cent_iff he2] at hg
      have h := walkK_sound split2_ok g
      rw [hg, Bool.not_true, Bool.false_or, ← he2, ← enc_mul h6, Bool.or_eq_true, ← hK2,
        ← hK2] at h
      exact h
    exact h

noncomputable def typeB_S6 : TypeBData S6G1 S6G2 where
  K₁ := S6K1
  K₂ := S6K2
  ε₁ := s6e1
  ε₂ := s6e2
  prod₁ := s6_prod₁
  prod₂ := s6_prod₂
  typeA := typeA_S6
  ε₁_mem := s6e1_mem_G2
  ε₂_mem := s6e2_mem_G1
  z_ne := s6z_ne
  z_mem := s6z_mem
  inf_split := s6_inf_split

theorem S6T_moved :
    ∀ x : S6, x ∈ S6G1 ⊓ S6G2 → x ≠ 1 → ∃ g : S6, g * x * g⁻¹ ∉ S6G1 ⊓ S6G2 := by
  have he1 : enc s6e1 = 4534800 := by decide +kernel
  have he2 : enc s6e2 = 4530945 := by decide +kernel
  have hT : ∀ g : S6, g ∈ S6G1 ⊓ S6G2 ↔ tK (enc g) = true := fun g => by
    rw [Subgroup.mem_inf, mem_S6G1, mem_S6G2, cent_iff he1, cent_iff he2, tK, Bool.and_eq_true]
  intro x hx h1
  have h := walkK_sound moved_ok x
  have hx1 : Nat.beq (enc x) oneS = false := by
    rw [← enc_oneS]
    exact beq_enc_false h6 h1
  rw [(hT x).1 hx, hx1, Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or] at h
  obtain ⟨g, hg⟩ := exists_of_walkK (P := fun d => !tK (conjK6 d (enc x)))
    (by simpa using h)
  have hg2 : tK (conjK6 (enc g) (enc x)) = false := by simpa using hg
  refine ⟨g, fun hg' => ?_⟩
  rw [hT, enc_conj6, hg2] at hg'
  exact absurd hg' (by decide)

theorem index_S6G1 : S6G1.index = 15 := by
  have h := Subgroup.index_mul_card S6G1
  rw [card_S6G1, card_S6] at h
  omega

theorem index_S6G2 : S6G2.index = 15 := by
  have h := Subgroup.index_mul_card S6G2
  rw [card_S6G2, card_S6] at h
  omega

theorem exists_sylow_S6T : ∃ S : Sylow 2 S6, (S : Subgroup S6) = S6G1 ⊓ S6G2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(S6G1 ⊓ S6G2) :=
    IsPGroup.of_card (n := 4) (by rw [card_S6T]; norm_num)
  have hidx : ¬ 2 ∣ (S6G1 ⊓ S6G2).index := by
    have h := Subgroup.index_mul_card (S6G1 ⊓ S6G2)
    rw [card_S6T, card_S6] at h
    omega
  exact ⟨hP.toSylow hidx, rfl⟩

theorem S6G1_ne_S6G2 : S6G1 ≠ S6G2 := by
  intro h
  have h1 : ∃ g : S6, g ∈ S6G1 ∧ g ∉ S6G2 := by decide +kernel
  obtain ⟨g, hg1, hg2⟩ := h1
  exact hg2 (h ▸ hg1)

theorem s6e1_ne : s6e1 ≠ 1 := by decide

theorem s6e2_ne : s6e2 ≠ 1 := by decide

theorem s6e1_sq : s6e1 ^ 2 = 1 := by decide

theorem s6e2_sq : s6e2 ^ 2 = 1 := by decide

theorem isP_zpowers_e1 : IsPGroup 2 (Subgroup.zpowers s6e1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : orderOf s6e1 = 2 := orderOf_eq_prime s6e1_sq s6e1_ne
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; norm_num)

theorem isP_zpowers_e2 : IsPGroup 2 (Subgroup.zpowers s6e2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : orderOf s6e2 = 2 := orderOf_eq_prime s6e2_sq s6e2_ne
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; norm_num)

theorem S6G1_le_normalizer : S6G1 ≤ Subgroup.normalizer (Subgroup.zpowers s6e1 : Set S6) := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  have hc : g * s6e1 * g⁻¹ = s6e1 := by
    rw [mem_S6G1.1 hg]; group
  rw [← conj_zpow, hc]
  exact Subgroup.zpow_mem_zpowers _ _

theorem S6G2_le_normalizer : S6G2 ≤ Subgroup.normalizer (Subgroup.zpowers s6e2 : Set S6) := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  have hc : g * s6e2 * g⁻¹ = s6e2 := by
    rw [mem_S6G2.1 hg]; group
  rw [← conj_zpow, hc]
  exact Subgroup.zpow_mem_zpowers _ _

theorem isTwoLocalAmalgam_S6 : IsTwoLocalAmalgam S6G1 S6G2 := by
  obtain ⟨S, hS⟩ := exists_sylow_S6T
  have hS' : ∀ x ∈ (S : Subgroup S6), x ≠ 1 → ∃ g : S6, g * x * g⁻¹ ∉ (S : Subgroup S6) := by
    rw [hS]
    exact S6T_moved
  exact ⟨isMaxTwoLocal_of_isCoatom S hS' S6G1 (Subgroup.zpowers s6e1)
      (isCoatom_of_index_fifteen S6G1 index_S6G1)
      (fun h => s6e1_ne (Subgroup.zpowers_eq_bot.1 h)) isP_zpowers_e1 S6G1_le_normalizer,
    isMaxTwoLocal_of_isCoatom S hS' S6G2 (Subgroup.zpowers s6e2)
      (isCoatom_of_index_fifteen S6G2 index_S6G2)
      (fun h => s6e2_ne (Subgroup.zpowers_eq_bot.1 h)) isP_zpowers_e2 S6G2_le_normalizer,
    S6G1_ne_S6G2, S, hS⟩

end CFSG.Quasithin.F6.GoldAmS
