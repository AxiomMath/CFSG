module

public import CFSG.LocalAnalysis.UniquenessCase.UC6M11Aut
public import CFSG.LocalAnalysis.UniquenessCase.UC6C626Cent
public import CFSG.LargeExtraspecial.S45QSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.ABGLocalTools
open CFSG.LargeExtraspecial.S45Q (card_dvd_factorial_index)
open CFSG.Sporadic.Schreier.M11Sylow (p0 q0)

namespace M11K

theorem dvd_card_of_closed_list {G : Type*} [Group G] (L : List G) (hnd : L.Nodup)
    (h1 : (1 : G) ∈ L) (hmul : ∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) (hinv : ∀ a ∈ L, a⁻¹ ∈ L)
    (K : Subgroup G) (hK : ∀ a ∈ L, a ∈ K) : L.length ∣ Nat.card K := by
  let H : Subgroup G :=
    { carrier := {a | a ∈ L}
      mul_mem' := fun {a b} ha hb => hmul a ha b hb
      one_mem' := h1
      inv_mem' := fun {a} ha => hinv a ha }
  have hH : H ≤ K := fun a ha => hK a ha
  have hcard : Nat.card H = L.length :=
    card_eq_length (fun a : G => a ∈ L) id Function.injective_id L hnd (fun b => by simp)
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hH

@[expose] def T1 : S11 := m11b * m11a * m11b * m11b * m11a * m11b * m11b * m11a * m11b

@[expose] def T2 : S11 := m11a * m11b * m11b * m11a * m11b * m11b * m11a * m11b * m11b

@[expose] def L8 : List S11 :=
  [1, T1, T2, T1 * T2, T2 * T1, T1 * T2 * T1, T2 * T1 * T2, T1 * T2 * T1 * T2]

theorem L8_nodup : L8.Nodup := by decide +kernel

theorem L8_mul : ∀ a ∈ L8, ∀ b ∈ L8, a * b ∈ L8 := by decide +kernel

theorem L8_inv : ∀ a ∈ L8, a⁻¹ ∈ L8 := by decide +kernel

theorem T1_comm : T1 * U = U * T1 := by decide +kernel

theorem T2_comm : T2 * V = V * T2 := by decide +kernel

theorem T1_swap : (T1 : Equiv.Perm (Fin 11)) p0 = q0 := by decide +kernel

theorem Elist_comm_U : ∀ e ∈ Elist, e * U = U * e := by decide +kernel

theorem Elist_trans : ∀ b b' : Fin 11, b ≠ p0 → b ≠ q0 → b' ≠ p0 → b' ≠ q0 →
    ∃ e ∈ Elist, (e : Equiv.Perm (Fin 11)) b = b' := by decide +kernel

theorem U_ne_one : U ≠ 1 := by decide +kernel

theorem V_ne_one : V ≠ 1 := by decide +kernel

theorem eleven_dvd_card (K : Subgroup S11)
    (htrans : ∀ y : Fin 11, ∃ k ∈ K, (k : Equiv.Perm (Fin 11)) p0 = y) : 11 ∣ Nat.card K := by
  have horb : MulAction.orbit K p0 = Set.univ := by
    ext y
    obtain ⟨k, hk, hky⟩ := htrans y
    exact ⟨fun _ => trivial, fun _ => ⟨⟨k, hk⟩, hky⟩⟩
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer K p0)
  rw [MulAction.index_stabilizer, horb, Set.ncard_univ] at h1
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  exact ⟨_, by rw [← h1]; ring⟩


theorem k626_m11 (K : Subgroup S11)
    (hK : ∀ x ∈ Eu, x ≠ 1 → ∀ c : S11, c * x = x * c → c ∈ K)
    (g : S11) (hgK : g ∈ K) (hg : orderOf g = 5 ∨ orderOf g = 11) : K = ⊤ := by
  have hEK : ∀ e ∈ Elist, e ∈ K := fun e he => hK U U_mem U_ne_one e (Elist_comm_U e he)
  have hT1 : T1 ∈ K := hK U U_mem U_ne_one T1 T1_comm
  have hT2 : T2 ∈ K := hK V V_mem V_ne_one T2 T2_comm
  have h9 : 9 ∣ Nat.card K := by
    have := dvd_card_of_closed_list Elist Elist_nodup (by decide +kernel) Elist_mul Elist_inv K hEK
    simpa [Elist] using this
  have h8 : 8 ∣ Nat.card K := by
    have := dvd_card_of_closed_list L8 L8_nodup (by decide +kernel) L8_mul L8_inv K (by
      intro a ha
      simp only [L8, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hT1
      · exact hT2
      · exact mul_mem hT1 hT2
      · exact mul_mem hT2 hT1
      · exact mul_mem (mul_mem hT1 hT2) hT1
      · exact mul_mem (mul_mem hT2 hT1) hT2
      · exact mul_mem (mul_mem (mul_mem hT1 hT2) hT1) hT2)
    simpa [L8] using this
  obtain ⟨k, hk, hkB⟩ : ∃ k ∈ K, (k : Equiv.Perm (Fin 11)) p0 ≠ p0 ∧
      (k : Equiv.Perm (Fin 11)) p0 ≠ q0 := by
    rcases move_pair g hg with h | h
    · exact ⟨g, hgK, h⟩
    · refine ⟨g * T1, mul_mem hgK hT1, ?_⟩
      have : ((g * T1 : S11) : Equiv.Perm (Fin 11)) p0 = (g : Equiv.Perm (Fin 11)) q0 := by
        simp [Subgroup.coe_mul, Equiv.Perm.mul_apply, T1_swap]
      rw [this]; exact h
  have h11 : 11 ∣ Nat.card K := by
    apply eleven_dvd_card
    intro y
    by_cases hy1 : y = p0
    · exact ⟨1, one_mem _, by simp [hy1]⟩
    by_cases hy2 : y = q0
    · exact ⟨T1, hT1, by rw [hy2]; exact T1_swap⟩
    obtain ⟨e, he, hey⟩ := Elist_trans _ y hkB.1 hkB.2 hy1 hy2
    refine ⟨e * k, mul_mem (hEK e he) hk, ?_⟩
    simpa [Subgroup.coe_mul, Equiv.Perm.mul_apply] using hey
  have h792 : 792 ∣ Nat.card K := by
    have h72 : 72 ∣ Nat.card K := (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h9)
    exact (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h72 h11)
  by_contra hne
  have hS : IsSimpleGroup S11 := fam_m11_simplicity.2.2
  have hfac := card_dvd_factorial_index hne
  have hcard : Nat.card K * K.index = 7920 := by
    rw [Subgroup.card_mul_index]; exact card_S11
  obtain ⟨a, ha⟩ := h792
  rw [ha] at hcard
  have hidx : K.index ∣ 10 := by
    have h' : 792 * (K.index * a) = 792 * 10 := by
      rw [show 792 * 10 = 7920 by norm_num, ← hcard]; ring
    exact ⟨a, (Nat.eq_of_mul_eq_mul_left (by norm_num) h').symm⟩
  have hidx1 : K.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
  rw [card_S11] at hfac
  have hmem : K.index ∈ Nat.divisors 10 := by simp [hidx]
  have h10 : Nat.divisors 10 = {1, 2, 5, 10} := by decide
  rw [h10] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact hidx1 h
  · rw [h] at hfac; norm_num [Nat.factorial] at hfac
  · rw [h] at hfac; norm_num [Nat.factorial] at hfac
  · rw [h] at hfac; norm_num [Nat.factorial] at hfac

theorem prime_order_cases (g : S11) {p : ℕ} (hp : p.Prime) (hgp : orderOf g = p) (hp3 : p ≠ 3) :
    orderOf g = 2 ∨ orderOf g = 5 ∨ orderOf g = 11 := by
  have hp7920 : p ∣ 7920 := by
    rw [← card_S11, ← hgp]; exact orderOf_dvd_natCard g
  have h7920 : (7920 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 * 11 := by norm_num
  rw [h7920] at hp7920
  rcases (Nat.Prime.dvd_mul hp).1 hp7920 with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact Or.inl (hgp.trans ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
          (hp.dvd_of_dvd_pow h)))
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)) hp3
    · exact Or.inr (Or.inl (hgp.trans ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)))
  · exact Or.inr (Or.inr (hgp.trans ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)))

theorem exists_conj_of_sylow {S : Type*} [Group S] [Finite S] {p : ℕ} [Fact p.Prime]
    (P1 P2 : Sylow p S) :
    ∃ g : S, ∀ x, x ∈ (P2 : Subgroup S) ↔ MulAut.conj g⁻¹ x ∈ (P1 : Subgroup S) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P1 P2
  refine ⟨g, fun x => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp

theorem sylow_of_card_nine (E : Subgroup S11) (hE : Nat.card E = 9) :
    ∃ P : Sylow 3 S11, (P : Subgroup S11) = E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE]; norm_num)
  have hidx : E.index = 880 := by
    have := Subgroup.card_mul_index E
    rw [hE, card_S11] at this
    omega
  exact ⟨hp.toSylow (by rw [hidx]; norm_num), IsPGroup.toSylow_coe _ _⟩

theorem Eu_isSylow : ∃ P : Sylow 3 S11, (P : Subgroup S11) = Eu :=
  sylow_of_card_nine Eu Eu_card

theorem exists_iso_sylow_m11 {X : Type} [Group X]
    (hX : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor X .M11) {E₀ : Subgroup X}
    (hE₀ : Nat.card E₀ = 9) : ∃ ψ : X ≃* S11, ∀ x, x ∈ E₀ ↔ ψ x ∈ Eu := by
  obtain ⟨φ0⟩ := hX
  let φ : X ≃* S11 := φ0
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE1 : Nat.card (E₀.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective]; exact hE₀
  obtain ⟨P1, hP1⟩ := sylow_of_card_nine _ hE1
  obtain ⟨P2, hP2⟩ := Eu_isSylow
  obtain ⟨γ, hγ⟩ := exists_conj_of_sylow P2 P1
  refine ⟨φ.trans (MulAut.conj γ⁻¹ : S11 ≃* S11), fun x => ?_⟩
  have h1 : x ∈ E₀ ↔ φ x ∈ (P1 : Subgroup S11) := by
    rw [hP1, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [h1, hγ, hP2]
  rfl

theorem k626_of_isSpor_m11 {X : Type} [Group X]
    (hX : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor X .M11) {E₀ : Subgroup X}
    (hE₀ : Nat.card E₀ = 9) (K : Subgroup X)
    (hK : ∀ x ∈ E₀, x ≠ 1 → ∀ c : X, c * x = x * c → c ∈ K)
    (g : X) (hgK : g ∈ K) (hg : orderOf g = 5 ∨ orderOf g = 11) : K = ⊤ := by
  obtain ⟨ψ, hψE⟩ := exists_iso_sylow_m11 hX hE₀
  let K' : Subgroup S11 := K.map ψ.toMonoidHom
  have hK' : ∀ x' ∈ Eu, x' ≠ 1 → ∀ c' : S11, c' * x' = x' * c' → c' ∈ K' := by
    intro x' hx' hx1 c' hc'
    have hx : ψ.symm x' ∈ E₀ := (hψE _).2 (by simpa using hx')
    have hx1' : ψ.symm x' ≠ 1 := fun h => hx1 (by simpa using congrArg ψ h)
    refine ⟨ψ.symm c', hK _ hx hx1' _ ?_, by simp⟩
    apply ψ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply, hc']
  have hg' : ψ g ∈ K' := ⟨g, hgK, rfl⟩
  have hgo : orderOf (ψ g) = 5 ∨ orderOf (ψ g) = 11 := by
    rw [MulEquiv.orderOf_eq]; exact hg
  have htop := k626_m11 K' hK' (ψ g) hg' hgo
  rw [eq_top_iff]
  intro x _
  have : ψ x ∈ K' := by rw [htop]; trivial
  obtain ⟨y, hy, hyx⟩ := this
  have : y = x := ψ.injective hyx
  rwa [← this]

end M11K

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)


theorem c626gen_of_m11 (h619 : m.C619) (h620 : m.C620) (hr3 : m.r = 3)
    (hX : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor m.Lbar .M11) : m.C626gen := by
  classical
  obtain ⟨φ0⟩ := id hX
  let φ : m.Lbar ≃* M11K.S11 := φ0
  have hcen : Subgroup.center m.Lbar = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv φ m11_center_eq_bot'
  have hE9 : Nat.card m.Ebar = 9 := by
    rw [m.card_Ebar h620, hr3]
    norm_num
  refine m.c626gen_of_Lbar_cent h619 h620 ?_ ?_
  · intro p hp hp2 hpr α hα
    obtain ⟨g, hg⟩ := M11K.allInner (MulAut.congr φ α)
    refine ⟨φ.symm g, ?_, ?_⟩
    · apply (MulAut.congr φ).injective
      rw [hg, congr_conj_uc6, MulEquiv.apply_symm_apply]
    · have h1 : MulAut.conj (φ.symm g) = α := by
        apply (MulAut.congr φ).injective
        rw [hg, congr_conj_uc6, MulEquiv.apply_symm_apply]
      rw [← hα, ← h1]
      exact (orderOf_injective _ (conj_injective_of_center_eq_bot hcen) (φ.symm g)).symm
  · intro K hK x hxK hxp hx2 hxr
    have hx3 : orderOf x ≠ 3 := hr3 ▸ hxr
    have hxo : orderOf (φ x) = orderOf x := MulEquiv.orderOf_eq φ x
    have hcases := M11K.prime_order_cases (φ x) hxp hxo hx3
    rw [hxo] at hcases
    have h511 : orderOf x = 5 ∨ orderOf x = 11 := by
      rcases hcases with h | h | h
      · exact absurd h hx2
      · exact Or.inl h
      · exact Or.inr h
    exact M11K.k626_of_isSpor_m11 hX hE9 K hK x hxK h511

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
