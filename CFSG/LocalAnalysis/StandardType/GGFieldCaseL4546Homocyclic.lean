module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Moving

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Homocyclic

variable {G : Type} [Group G]

theorem card_sup_eq_mul_of_inf_eq_bot {P Q : Subgroup G}
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (h : P ⊓ Q = ⊥) :
    Nat.card ↥(P ⊔ Q) = Nat.card P * Nat.card Q := by
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right P Q hPQ
  let f : P × Q → ↥(P ⊔ Q) := fun ab => ⟨ab.1 * ab.2, Subgroup.mul_mem_sup ab.1.2 ab.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      have e : (a : G) * b = a' * b' := congrArg Subtype.val hab
      have h1 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [e]
          _ = b' * (b : G)⁻¹ := by group
      have hmem : (a' : G)⁻¹ * a ∈ P ⊓ Q :=
        ⟨P.mul_mem (P.inv_mem a'.2) a.2, h1 ▸ Q.mul_mem b'.2 (Q.inv_mem b.2)⟩
      rw [h, Subgroup.mem_bot] at hmem
      have ha : (a : G) = a' := by
        calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
          _ = a' := by rw [hmem, mul_one]
      have hb : (b : G) = b' := by
        rw [ha] at e
        exact mul_left_cancel e
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
    · rintro ⟨g, hg⟩
      have hg' : g ∈ ((P ⊔ Q : Subgroup G) : Set G) := hg
      rw [hcoe] at hg'
      obtain ⟨a, ha, b, hb, rfl⟩ := hg'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_eq_of_bijective f hf).symm

theorem mem_zpowers_pow_of_pow_eq_one [Finite G] {p s : ℕ} (hp : p.Prime) (hs : 1 ≤ s)
    {u e : G} (hu : orderOf u = p ^ s) (he : e ∈ Subgroup.zpowers u) (hep : e ^ p = 1) :
    e ∈ Subgroup.zpowers (u ^ p ^ (s - 1)) := by
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_iff_mem_zpowers.mpr he)
  have h1 : orderOf u ∣ k * p := orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact hep)
  rw [hu, show p ^ s = p ^ (s - 1) * p by rw [← pow_succ, Nat.sub_add_cancel hs]] at h1
  obtain ⟨m, hm⟩ := Nat.dvd_of_mul_dvd_mul_right hp.pos h1
  rw [hm, pow_mul]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m

variable [Finite G]

theorem ggHomocyclic_step {p s : ℕ} (hp : p.Prime) (hs : 1 ≤ s) {A Ω : Subgroup G}
    (hab : IsMulCommutative A) (hexp : ∀ a ∈ A, a ^ p ^ s = 1)
    (hΩ : ∀ g : G, g ∈ Ω ↔ g ∈ A ∧ g ^ p = 1) {H : Subgroup G} {n : ℕ} (hHA : H ≤ A)
    (hH : Nat.card H = p ^ (s * n)) (hHΩ : Nat.card (H ⊓ Ω : Subgroup G) = p ^ n)
    (hHO : H ⊓ Ω ≤ ggPowSubgroup A hab (p ^ (s - 1)))
    (hlt : p ^ n < Nat.card (ggPowSubgroup A hab (p ^ (s - 1)))) :
    ∃ H' : Subgroup G, H' ≤ A ∧ Nat.card H' = p ^ (s * (n + 1)) ∧
      Nat.card (H' ⊓ Ω : Subgroup G) = p ^ (n + 1) ∧
      H' ⊓ Ω ≤ ggPowSubgroup A hab (p ^ (s - 1)) := by
  have : Fact p.Prime := ⟨hp⟩
  set O := ggPowSubgroup A hab (p ^ (s - 1)) with hO
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hOΩ : O ≤ Ω := by
    rintro _ ⟨u, hu, rfl⟩
    refine (hΩ _).mpr ⟨A.pow_mem hu _, ?_⟩
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hs, hexp u hu]
  obtain ⟨o, hoO, hoH⟩ : ∃ o ∈ O, o ∉ H := by
    by_contra hcon
    push Not at hcon
    have hle : O ≤ H ⊓ Ω := fun o ho => ⟨hcon o ho, hOΩ ho⟩
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨u, huA, rfl⟩ := hoO
  have ho1 : u ^ p ^ (s - 1) ≠ 1 := fun h => hoH (h ▸ H.one_mem)
  have hou : orderOf u = p ^ s := by
    have h := orderOf_eq_prime_pow ho1 (by rw [Nat.sub_add_cancel hs]; exact hexp u huA)
    rwa [Nat.sub_add_cancel hs] at h
  have hop : (u ^ p ^ (s - 1)) ^ p = 1 := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hs, hexp u huA]
  have hHu : H ⊓ Subgroup.zpowers u = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    by_contra hz1
    obtain ⟨m, he1, hep⟩ := exists_pow_pow_ne_one ⟨s, hexp z (hHA hz.1)⟩ hz1
    have heH : z ^ p ^ m ∈ H := H.pow_mem hz.1 _
    have heu : z ^ p ^ m ∈ Subgroup.zpowers u := Subgroup.pow_mem _ hz.2 _
    have he := mem_zpowers_pow_of_pow_eq_one hp hs hou heu hep
    have heq := zpowers_eq_of_mem_of_ne_one hop he he1
    apply hoH
    exact (Subgroup.zpowers_le.mpr heH) (heq ▸ Subgroup.mem_zpowers _)
  have hcN : ∀ S : Subgroup G, S ≤ A → ∀ w ∈ A,
      S ≤ Subgroup.normalizer (Subgroup.zpowers w : Set G) := fun S hSA w hw h hh =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.zpow_left (hcomm w hw h (hSA hh) : Commute w h) k).eq)
  have hHN := hcN H hHA u huA
  have hoA : u ^ p ^ (s - 1) ∈ A := A.pow_mem huA _
  have hou' : Subgroup.zpowers (u ^ p ^ (s - 1)) ≤ Subgroup.zpowers u :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) _)
  have hΩeq : (H ⊔ Subgroup.zpowers u) ⊓ Ω =
      (H ⊓ Ω) ⊔ Subgroup.zpowers (u ^ p ^ (s - 1)) := by
    refine le_antisymm ?_ (sup_le (inf_le_inf_right _ le_sup_left)
      (Subgroup.zpowers_le.mpr ⟨Subgroup.mem_sup_right (Subgroup.pow_mem _
        (Subgroup.mem_zpowers u) _), hOΩ ⟨u, huA, rfl⟩⟩))
    intro g hg
    have hg' : g ∈ ((H ⊔ Subgroup.zpowers u : Subgroup G) : Set G) := hg.1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHN] at hg'
    obtain ⟨h, hh, z, hz, rfl⟩ := hg'
    have hzA : z ∈ A := (Subgroup.zpowers_le.mpr huA) hz
    have hgp := ((hΩ _).mp hg.2).2
    rw [(Commute.mul_pow (hcomm h (hHA hh) z hzA : Commute h z) p)] at hgp
    have hzp : z ^ p ∈ H ⊓ Subgroup.zpowers u := by
      refine ⟨?_, Subgroup.pow_mem _ hz _⟩
      have : z ^ p = (h ^ p)⁻¹ := eq_inv_of_mul_eq_one_right hgp
      rw [this]
      exact H.inv_mem (H.pow_mem hh _)
    rw [hHu, Subgroup.mem_bot] at hzp
    have hhp : h ^ p = 1 := by rw [hzp, mul_one] at hgp; exact hgp
    exact Subgroup.mul_mem_sup ⟨hh, (hΩ h).mpr ⟨hHA hh, hhp⟩⟩
      (mem_zpowers_pow_of_pow_eq_one hp hs hou hz hzp)
  have hinf2 : (H ⊓ Ω) ⊓ Subgroup.zpowers (u ^ p ^ (s - 1)) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf inf_le_left hou').trans hHu.le)
  refine ⟨H ⊔ Subgroup.zpowers u, sup_le hHA (Subgroup.zpowers_le.mpr huA), ?_, ?_, ?_⟩
  · rw [card_sup_eq_mul_of_inf_eq_bot hHN hHu, hH, Nat.card_zpowers, hou, mul_add, mul_one,
      pow_add]
  · rw [hΩeq, card_sup_eq_mul_of_inf_eq_bot (hcN _ (inf_le_left.trans hHA) _ hoA) hinf2, hHΩ,
      Nat.card_zpowers, orderOf_eq_prime hop ho1, pow_succ]
  · rw [hΩeq]
    exact sup_le hHO (Subgroup.zpowers_le.mpr ⟨u, huA, rfl⟩)

theorem exists_ggHomocyclic {p s : ℕ} (hp : p.Prime) (hs : 1 ≤ s) {A Ω : Subgroup G}
    (hab : IsMulCommutative A) (hexp : ∀ a ∈ A, a ^ p ^ s = 1)
    (hΩ : ∀ g : G, g ∈ Ω ↔ g ∈ A ∧ g ^ p = 1) {r : ℕ}
    (hr : Nat.card (ggPowSubgroup A hab (p ^ (s - 1))) = p ^ r) :
    ∃ H : Subgroup G, H ≤ A ∧ Nat.card H = p ^ (s * r) ∧
      Nat.card (H ⊓ Ω : Subgroup G) = p ^ r := by
  have key : ∀ n ≤ r, ∃ H : Subgroup G, H ≤ A ∧ Nat.card H = p ^ (s * n) ∧
      Nat.card (H ⊓ Ω : Subgroup G) = p ^ n ∧ H ⊓ Ω ≤ ggPowSubgroup A hab (p ^ (s - 1)) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨⊥, bot_le, by simp, by simp, by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨H, hHA, hH, hHΩ, hHO⟩ := ih (by omega)
      exact ggHomocyclic_step hp hs hab hexp hΩ hHA hH hHΩ hHO
        (by rw [hr]; exact Nat.pow_lt_pow_right hp.one_lt (by omega))
  obtain ⟨H, hHA, hH, hHΩ, -⟩ := key r le_rfl
  exact ⟨H, hHA, hH, hHΩ⟩

end Homocyclic

end CFSG.StandardType

end
