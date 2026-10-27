module

public import CFSG.Quasithin.H13.U3L14D6

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Blocks

variable {V : Type} [CommGroup V]

theorem dihedral_three_eq_or_eq_inv :
    ∀ a b : DihedralGroup 3, a ≠ 1 → a ^ 3 = 1 → b ≠ 1 → b ^ 3 = 1 → b = a ∨ b = a⁻¹ := by
  decide

theorem sq_conj_eq_of_dihedral {L : Subgroup (MulAut V)}
    (hL : Nonempty (↥L ≃* DihedralGroup 3)) {x t : MulAut V}
    (hx : ∀ l ∈ L, x * l * x⁻¹ ∈ L) (ht : t ∈ L) (ht1 : t ≠ 1) (ht3 : t ^ 3 = 1) :
    x ^ 2 * t * (x ^ 2)⁻¹ = t := by
  obtain ⟨e⟩ := hL
  have hsL : x * t * x⁻¹ ∈ L := hx t ht
  have hs1 : x * t * x⁻¹ ≠ 1 := by
    intro h
    apply ht1
    calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  have hs3 : (x * t * x⁻¹) ^ 3 = 1 := by
    have e1 : (x * t * x⁻¹) ^ 3 = x * t ^ 3 * x⁻¹ := by
      rw [pow_three, pow_three]
      group
    rw [e1, ht3]
    group
  have hne : ∀ {s : MulAut V} (hs : s ∈ L), s ≠ 1 → e ⟨s, hs⟩ ≠ 1 := by
    intro s hs hs1 h
    apply hs1
    have := e.injective (h.trans e.map_one.symm)
    exact congrArg Subtype.val this
  have hpow : ∀ {s : MulAut V} (hs : s ∈ L), s ^ 3 = 1 → e ⟨s, hs⟩ ^ 3 = 1 := by
    intro s hs h3
    rw [← map_pow]
    have : (⟨s, hs⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [this, map_one]
  have e2 : x ^ 2 * t * (x ^ 2)⁻¹ = x * (x * t * x⁻¹) * x⁻¹ := by
    rw [sq]
    group
  rcases dihedral_three_eq_or_eq_inv (e ⟨t, ht⟩) (e ⟨x * t * x⁻¹, hsL⟩) (hne ht ht1)
      (hpow ht ht3) (hne hsL hs1) (hpow hsL hs3) with h | h
  · have hs : x * t * x⁻¹ = t := congrArg Subtype.val (e.injective h)
    rw [e2, hs, hs]
  · have hs : x * t * x⁻¹ = t⁻¹ := by
      have h' : e ⟨x * t * x⁻¹, hsL⟩ = e (⟨t, ht⟩⁻¹) := by rw [h, map_inv]
      exact congrArg Subtype.val (e.injective h')
    rw [e2, hs]
    calc x * t⁻¹ * x⁻¹ = (x * t * x⁻¹)⁻¹ := by group
      _ = t := by rw [hs, inv_inv]

theorem false_of_blocks {X Tb Pb L₁ L₂ : Subgroup (MulAut V)}
    (hB : Blocks14612 X Tb Pb 3 L₁ L₂) (hTb : Tb ≤ X) (hcard : Nat.card Pb = 9)
    (hexp : ∀ z ∈ Pb, z ^ 3 = 1) {x₁ x₂ : MulAut V} (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X)
    (h₁ : ∀ z ∈ Pb, x₁ ^ 2 * z * (x₁ ^ 2)⁻¹ = z⁻¹)
    (h₂ : ∀ z ∈ Pb, x₂ ^ 2 * z * (x₂ ^ 2)⁻¹ = z⁻¹)
    (h₁₂ : ∀ z ∈ Pb, (x₁ * x₂) ^ 2 * z * ((x₁ * x₂) ^ 2)⁻¹ = z⁻¹) : False := by
  obtain ⟨t₀, ht₀, hswap⟩ := hB.swap
  have hL₂ : ∀ x ∈ X, conjBy x L₂ = L₁ ∨ conjBy x L₂ = L₂ := by
    intro x hx
    rcases hB.orb _ (mul_mem hx (hTb ht₀)) with h | h <;> rw [← conjBy_conjBy, hswap] at h
    · exact Or.inl h
    · exact Or.inr h
  have hfix : ∀ x ∈ X, conjBy x L₁ = L₁ → conjBy x L₂ = L₂ := by
    intro x hx h
    rcases hL₂ x hx with h' | h'
    · exact absurd (conjBy_injective x (h'.trans h.symm)) hB.ne
    · exact h'
  have hsw : ∀ x ∈ X, conjBy x L₁ = L₂ → conjBy x L₂ = L₁ := by
    intro x hx h
    rcases hL₂ x hx with h' | h'
    · exact h'
    · exact absurd (conjBy_injective x (h'.trans h.symm)) hB.ne
  have hL₂N : L₂ ≤ normalizer (L₁ : Set (MulAut V)) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      have e : a * l * a⁻¹ = l := by rw [← hB.comm l hl a ha]; group
      rw [e]
      exact hl
    · intro hl
      have e : l = a * l * a⁻¹ := by
        calc l = a⁻¹ * (a * l * a⁻¹) * a := by group
          _ = a⁻¹ * (a * (a * l * a⁻¹)) := by rw [mul_assoc, hB.comm _ hl a ha]
          _ = a * l * a⁻¹ := by group
      rw [e]
      exact hl
  have key : ∀ x ∈ X, (∀ z ∈ Pb, x ^ 2 * z * (x ^ 2)⁻¹ = z⁻¹) → conjBy x L₁ = L₂ := by
    intro x hx hinv
    rcases hB.orb x hx with h1 | h1
    · exfalso
      have h2 := hfix x hx h1
      have hn : ∀ {L : Subgroup (MulAut V)}, conjBy x L = L → ∀ l ∈ L, x * l * x⁻¹ ∈ L := by
        intro L hL l hl
        rw [← hL, mem_conjBy_iff]
        have e : x⁻¹ * (x * l * x⁻¹) * x = l := by group
        rw [e]
        exact hl
      have hn2 : ∀ {L : Subgroup (MulAut V)}, conjBy x L = L → ∀ l ∈ L,
          x ^ 2 * l * (x ^ 2)⁻¹ ∈ L := by
        intro L hL l hl
        have h3 := hn hL _ (hn hL l hl)
        have e : x * (x * l * x⁻¹) * x⁻¹ = x ^ 2 * l * (x ^ 2)⁻¹ := by
          rw [sq]
          group
        rwa [e] at h3
      obtain ⟨z, hzP, hzL⟩ : ∃ z ∈ Pb, z ∉ L₂ := by
        by_contra hcon
        push Not at hcon
        obtain ⟨e₂⟩ := hB.dih₂
        have hd := Subgroup.card_dvd_of_le (show Pb ≤ L₂ from hcon)
        rw [hcard, Nat.card_congr e₂.toEquiv, DihedralGroup.nat_card] at hd
        norm_num at hd
      obtain ⟨l, hl, a, ha, rfl⟩ := exists_mul_of_mem_sup hL₂N (hB.P_le hzP)
      have hla : l * a = a * l := hB.comm l hl a ha
      have hl1 : l ≠ 1 := by
        rintro rfl
        exact hzL (by simpa using ha)
      have hl3 : l ^ 3 = 1 := by
        have h3 := hexp _ hzP
        rw [(Commute.mul_pow hla 3)] at h3
        have hmem : l ^ 3 ∈ L₁ ⊓ L₂ := by
          refine mem_inf.2 ⟨pow_mem hl 3, ?_⟩
          rw [eq_inv_of_mul_eq_one_left h3]
          exact inv_mem (pow_mem ha 3)
        rw [hB.inf, mem_bot] at hmem
        exact hmem
      have hinvl : x ^ 2 * l * (x ^ 2)⁻¹ = l⁻¹ := by
        have h4 := hinv _ hzP
        have hl' : x ^ 2 * l * (x ^ 2)⁻¹ ∈ L₁ := hn2 h1 l hl
        have ha' : x ^ 2 * a * (x ^ 2)⁻¹ ∈ L₂ := hn2 h2 a ha
        have e1 : x ^ 2 * (l * a) * (x ^ 2)⁻¹ =
            (x ^ 2 * l * (x ^ 2)⁻¹) * (x ^ 2 * a * (x ^ 2)⁻¹) := by group
        rw [e1] at h4
        have e2 : l * (x ^ 2 * l * (x ^ 2)⁻¹) = a⁻¹ * (x ^ 2 * a * (x ^ 2)⁻¹)⁻¹ := by
          calc l * (x ^ 2 * l * (x ^ 2)⁻¹) =
              l * ((x ^ 2 * l * (x ^ 2)⁻¹) * (x ^ 2 * a * (x ^ 2)⁻¹)) *
                (x ^ 2 * a * (x ^ 2)⁻¹)⁻¹ := by group
            _ = l * (a * l)⁻¹ * (x ^ 2 * a * (x ^ 2)⁻¹)⁻¹ := by rw [h4, hla]
            _ = a⁻¹ * (x ^ 2 * a * (x ^ 2)⁻¹)⁻¹ := by group
        have hmem : l * (x ^ 2 * l * (x ^ 2)⁻¹) ∈ L₁ ⊓ L₂ := by
          refine mem_inf.2 ⟨mul_mem hl hl', ?_⟩
          rw [e2]
          exact mul_mem (inv_mem ha) (inv_mem ha')
        rw [hB.inf, mem_bot] at hmem
        calc x ^ 2 * l * (x ^ 2)⁻¹ = l⁻¹ * (l * (x ^ 2 * l * (x ^ 2)⁻¹)) := by group
          _ = l⁻¹ := by rw [hmem, mul_one]
      rw [sq_conj_eq_of_dihedral hB.dih₁ (hn h1) hl hl1 hl3] at hinvl
      apply hl1
      have hl2 : l ^ 2 = 1 := by
        rw [sq]
        nth_rewrite 2 [hinvl]
        exact mul_inv_cancel l
      have e3 : l ^ 3 = l ^ 2 * l := pow_succ l 2
      rw [hl2, one_mul, hl3] at e3
      exact e3.symm
    · exact h1
  have k₁ := key x₁ hx₁ h₁
  have k₂ := key x₂ hx₂ h₂
  have k₁₂ := key (x₁ * x₂) (mul_mem hx₁ hx₂) h₁₂
  rw [← conjBy_conjBy, k₂, hsw x₁ hx₁ k₁] at k₁₂
  exact hB.ne k₁₂.symm

end Blocks

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_le_of_relIndex_eq_sq {P K : Subgroup G} (hKP : K ≤ P)
    (hn : P ≤ normalizer (K : Set G)) {p : ℕ} [Fact p.Prime] (h : K.relIndex P = p ^ 2) :
    ⁅P, P⁆ ≤ K := by
  have : (K.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hKP).2 hn
  have hc : Nat.card (↥P ⧸ K.subgroupOf P) = p ^ 2 := by
    rw [← index_eq_card]
    exact h
  have hcomm : IsMulCommutative (↥P ⧸ K.subgroupOf P) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hc
  rw [commutator_le]
  intro a ha b hb
  have h1 : (QuotientGroup.mk ⟨a, ha⟩ : ↥P ⧸ K.subgroupOf P) * QuotientGroup.mk ⟨b, hb⟩ =
      QuotientGroup.mk ⟨b, hb⟩ * QuotientGroup.mk ⟨a, ha⟩ :=
    hcomm.is_comm.comm _ _
  have h2 : (QuotientGroup.mk ((⟨a, ha⟩ : ↥P) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥P)⁻¹ * (⟨b, hb⟩ : ↥P)⁻¹) :
      ↥P ⧸ K.subgroupOf P) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, h1]
    group
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h2
  rw [commutatorElement_def]
  simpa using h2

theorem false_of_q8 {T P W : Subgroup G} (hP : IsXi T P)
    (h9 : (pCoreOf 2 P).relIndex P = 9) (hexp : ∀ y ∈ P, y ^ 3 ∈ pCoreOf 2 P)
    (hT : IsSylowTwoOf T (P ⊔ T)) (hW : IsTwoReducedIn (P ⊔ T) W)
    (hWP : W ⊓ centralizer (P : Set G) = ⊥) (hW1 : W ≠ ⊥)
    (hgen : W ≤ conjClosure (W ⊓ centralizer (T : Set G)) (P ⊔ T))
    (hq : qhatInt (P ⊔ T) W hW.2.2.1 ≤ 2)
    (hsq : CFSG.Open.SQTKTauCeti.StronglyQuasithin ↥(P ⊔ T))
    (hkg : CFSG.SectionRank.IsKGroupCat ↥(P ⊔ T))
    {b₁ b₂ : G} (hb₁ : b₁ ∈ T) (hb₂ : b₂ ∈ T)
    (h₁ : ∀ y ∈ P, b₁ ^ 2 * y * (b₁ ^ 2)⁻¹ * y ∈ ⁅P, P⁆ ⊔ pCoreOf 2 P)
    (h₂ : ∀ y ∈ P, b₂ ^ 2 * y * (b₂ ^ 2)⁻¹ * y ∈ ⁅P, P⁆ ⊔ pCoreOf 2 P)
    (h₁₂ : ∀ y ∈ P, (b₁ * b₂) ^ 2 * y * ((b₁ * b₂) ^ 2)⁻¹ * y ∈ ⁅P, P⁆ ⊔ pCoreOf 2 P)
    (hc : ∃ y ∈ P, ⁅b₁, b₂⁆ * y * ⁅b₁, b₂⁆⁻¹ * y⁻¹ ∉ ⁅P, P⁆ ⊔ pCoreOf 2 P) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTP : T ≤ normalizer (P : Set G) := hP.2.1
  have hab : ⁅P, P⁆ ≤ pCoreOf 2 P :=
    commutator_le_of_relIndex_eq_sq (LieType.BorelTits.pCoreOf_le 2 P)
      (LieType.BorelTits.le_normalizer_pCoreOf 2 P) (p := 3) (by rw [h9]; norm_num)
  have hsup : ⁅P, P⁆ ⊔ pCoreOf 2 P = pCoreOf 2 P := sup_eq_right.2 hab
  rw [hsup] at h₁ h₂ h₁₂ hc
  have hN : P ⊔ T ≤ normalizer (W : Set G) := hW.2.1
  have hPW : ¬ P ≤ centralizer (W : Set G) := by
    intro h
    apply hW1
    rw [eq_bot_iff, ← hWP]
    exact le_inf le_rfl (le_centralizer_iff.1 h)
  have hC : P ⊓ centralizer (W : Set G) ≤ pCoreOf 2 P :=
    inf_centralizer_le_of_isXi hP hab (le_sup_right.trans hN) (le_sup_left.trans hN) hPW
  have hO2W : pCoreOf 2 P ≤ centralizer (W : Set G) :=
    (pCoreOf_le_pCoreOf_sup_of_le hTP).trans (pCoreOf_le_centralizer_of_reduced hW)
  have hPC : P ⊓ centralizer (W : Set G) = pCoreOf 2 P :=
    le_antisymm hC (le_inf (LieType.BorelTits.pCoreOf_le 2 P) hO2W)
  have hnorm : ∀ S : Subgroup ↥(P ⊔ T), S.Normal →
      P ⊔ T ≤ normalizer ((S.map (P ⊔ T).subtype : Subgroup G) : Set G) := by
    intro S hS
    have h1 : (S.map (P ⊔ T).subtype).subgroupOf (P ⊔ T) = S :=
      Subgroup.comap_map_eq_self_of_injective (P ⊔ T).subtype_injective S
    have h2 : ((S.map (P ⊔ T).subtype).subgroupOf (P ⊔ T)).Normal := by
      rw [h1]
      exact hS
    exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le S)).1 h2
  let _ : CommGroup ↥W := commGroupOfElemAbelian hW.2.2.1
  have hsqW : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hW.2.2.1.2 v v.2)
  have hPn' : (P.subgroupOf (P ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hTP)
  have hmap : (P.subgroupOf (P ⊔ T) ⊔ (actW hN).ker).map (actW hN) =
      (P.subgroupOf (P ⊔ T)).map (actW hN) := by
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 le_rfl, sup_bot_eq]
  have hker : (actW hN).ker = (centralizer (W : Set G)).subgroupOf (P ⊔ T) := by
    ext x
    rw [MonoidHom.mem_ker, actW_eq_one_iff, mem_subgroupOf]
  have hcard9 : Nat.card ↥((P.subgroupOf (P ⊔ T) ⊔ (actW hN).ker).map (actW hN)) = 9 := by
    rw [hmap, ← relIndex_ker, hker, relIndex_subgroupOf le_sup_left, ← inf_relIndex_right,
      inf_comm, hPC, h9]
  have hexp3 : ∀ z ∈ (P.subgroupOf (P ⊔ T) ⊔ (actW hN).ker).map (actW hN), z ^ 3 = 1 := by
    intro z hz
    rw [hmap] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    rw [← map_pow, actW_eq_one_iff]
    exact hO2W (by simpa using hexp a (mem_subgroupOf.1 ha))
  have hinv : ∀ b (hb : b ∈ P ⊔ T), (∀ y ∈ P, b ^ 2 * y * (b ^ 2)⁻¹ * y ∈ pCoreOf 2 P) →
      ∀ z ∈ (P.subgroupOf (P ⊔ T) ⊔ (actW hN).ker).map (actW hN),
        actW hN ⟨b, hb⟩ ^ 2 * z * (actW hN ⟨b, hb⟩ ^ 2)⁻¹ = z⁻¹ := by
    intro b hb hby z hz
    rw [hmap] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have h1 : actW hN ((⟨b, hb⟩ : ↥(P ⊔ T)) ^ 2 * a * ((⟨b, hb⟩ : ↥(P ⊔ T)) ^ 2)⁻¹ * a) = 1 := by
      rw [actW_eq_one_iff]
      exact hO2W (by simpa using hby a (mem_subgroupOf.1 ha))
    rw [map_mul, map_mul, map_mul, map_inv, map_pow] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hstr : PStr14612 (actW hN).range ((T.subgroupOf (P ⊔ T)).map (actW hN))
      ((P.subgroupOf (P ⊔ T) ⊔ (actW hN).ker).map (actW hN)) 3 := by
    refine pstr_of_hom hsqW (actW hN) (P.subgroupOf (P ⊔ T) ⊔ (actW hN).ker)
      (T.subgroupOf (P ⊔ T)) Nat.prime_three (by norm_num) ?_ ?_ ?_ le_sup_right ?_ ?_ ?_
      hT.2.2 ?_ ?_ (by rw [hcard9]; norm_num) ?_ ?_
    ·
      intro x hx
      have hxC := (actW_eq_one_iff hN x).1 hx
      obtain ⟨k, hk⟩ := isPGroup_inf_centralizer hT.2.1 hTP hC ⟨x, x.2, hxC⟩
      refine ⟨k, Subtype.ext ?_⟩
      simpa using congrArg Subtype.val hk
    ·
      intro S hS hS2 x hx
      rw [actW_eq_one_iff]
      have hle : S.map (P ⊔ T).subtype ≤ pCoreOf 2 (P ⊔ T) :=
        LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (map_subtype_le S) (hnorm S hS)
          (hS2.map _)
      exact pCoreOf_le_centralizer_of_reduced hW (hle ⟨x, hx, rfl⟩)
    · exact Subgroup.sup_normal _ _
    ·
      intro x hx
      have hle : P.subgroupOf (P ⊔ T) ⊔ (actW hN).ker ≤
          ((P.subgroupOf (P ⊔ T)).map (actW hN)).comap (actW hN) :=
        sup_le (le_comap_map _ _) (MonoidHom.ker_le_comap _ _)
      obtain ⟨a, ha, hax⟩ := hle hx
      refine ⟨1, ?_⟩
      rw [pow_one, map_pow, ← hax, ← map_pow, actW_eq_one_iff]
      exact hO2W (by simpa using hexp a (mem_subgroupOf.1 ha))
    ·
      have h1 : P.subgroupOf (P ⊔ T) ⊔ T.subgroupOf (P ⊔ T) = ⊤ := by
        rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
      rw [eq_top_iff, ← h1]
      exact sup_le_sup_right le_sup_left _
    · exact hT.2.1.comap_of_injective (P ⊔ T).subtype (P ⊔ T).subtype_injective
    ·
      intro N hNn hkN hNP
      have hP' := hP
      obtain ⟨-, -, -, p, -, -, -, -, hirr⟩ := hP'
      have hO2N : pCoreOf 2 P ≤ N.map (P ⊔ T).subtype := by
        intro o ho
        exact ⟨⟨o, mem_sup_left (LieType.BorelTits.pCoreOf_le 2 P ho)⟩,
          hkN ((actW_eq_one_iff hN _).2 (hO2W ho)), rfl⟩
      have hTY : T ≤ normalizer
          (((N.map (P ⊔ T).subtype ⊓ P) ⊔ pCoreOf 2 P : Subgroup G) : Set G) := by
        intro t ht
        exact inf_normalizer_le_normalizer_sup _ _ ⟨inf_normalizer_le_normalizer_inf
          ⟨hnorm N hNn (mem_sup_right ht), hTP ht⟩,
          LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P (hTP ht)⟩
      rcases hirr ((N.map (P ⊔ T).subtype ⊓ P) ⊔ pCoreOf 2 P) (by rw [hsup]; exact le_sup_right)
          (sup_le inf_le_right (LieType.BorelTits.pCoreOf_le 2 P)) hTY with h | h
      · left
        refine le_antisymm (fun n hn => ?_) hkN
        have hn' : n ∈ ((P.subgroupOf (P ⊔ T) ⊔ (actW hN).ker : Subgroup ↥(P ⊔ T)) :
            Set ↥(P ⊔ T)) := hNP hn
        rw [mul_normal] at hn'
        obtain ⟨a, ha, k, hk, rfl⟩ := hn'
        have haN : a ∈ N := by
          have e : a = (a * k) * k⁻¹ := by group
          rw [e]
          exact mul_mem hn (inv_mem (hkN hk))
        have haY : (a : G) ∈ (N.map (P ⊔ T).subtype ⊓ P) ⊔ pCoreOf 2 P :=
          mem_sup_left ⟨⟨a, haN, rfl⟩, mem_subgroupOf.1 ha⟩
        rw [h, hsup] at haY
        exact mul_mem ((actW_eq_one_iff hN a).2 (hO2W haY)) hk
      · right
        refine le_antisymm hNP (sup_le (fun a ha => ?_) hkN)
        have haY : (a : G) ∈ (N.map (P ⊔ T).subtype ⊓ P) ⊔ pCoreOf 2 P := by
          rw [h]
          exact mem_subgroupOf.1 ha
        obtain ⟨b, hb, hba⟩ := (sup_le inf_le_left hO2N) haY
        have e : b = a := Subtype.ext hba
        rw [← e]
        exact hb
    ·
      intro h
      apply hPW
      intro y hy
      exact (actW_eq_one_iff hN ⟨y, mem_sup_left hy⟩).1 (h (mem_sup_left (mem_subgroupOf.2 hy)))
    · rw [range_actW]
      exact hq
    · exact ⟨↥(P ⊔ T), inferInstance, inferInstance, fun p hp hp2 => hsq p hp hp2, hkg,
        (actW hN).rangeRestrict, (actW hN).rangeRestrict_surjective⟩
  have hfix : fixV ((P.subgroupOf (P ⊔ T) ⊔ (actW hN).ker).map (actW hN)) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hwP : (w : G) ∈ centralizer (P : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := hw (actW hN ⟨y, mem_sup_left hy⟩)
        ⟨⟨y, mem_sup_left hy⟩, mem_sup_left (mem_subgroupOf.2 hy), rfl⟩
      have h2 := congrArg Subtype.val h1
      rw [actW_apply_coe] at h2
      calc y * (w : G) = (y * w * y⁻¹) * y := by group
        _ = w * y := by rw [h2]
    have h3 : (w : G) ∈ W ⊓ centralizer (P : Set G) := ⟨w.2, hwP⟩
    rw [hWP, mem_bot] at h3
    exact mem_bot.2 (Subtype.ext h3)
  have hgen' : ∀ W' : Subgroup ↥W, (∀ g ∈ (actW hN).range,
      ∀ z ∈ fixV ((T.subgroupOf (P ⊔ T)).map (actW hN)), g z ∈ W') → W' = ⊤ := by
    intro W' hW'
    have hle : W ≤ W'.map W.subtype := by
      refine hgen.trans (conjClosure_le fun g hg c hc => ?_)
      have hcfix : (⟨c, (mem_inf.1 hc).1⟩ : ↥W) ∈ fixV ((T.subgroupOf (P ⊔ T)).map (actW hN)) := by
        rintro _ ⟨t, ht, rfl⟩
        apply Subtype.ext
        rw [actW_apply_coe]
        have htc : (t : G) * c = c * t :=
          mem_centralizer_iff.1 (mem_inf.1 hc).2 (t : G) (mem_subgroupOf.1 ht)
        show (t : G) * c * (t : G)⁻¹ = c
        rw [htc]
        group
      exact ⟨actW hN ⟨g, hg⟩ ⟨c, (mem_inf.1 hc).1⟩, hW' _ ⟨⟨g, hg⟩, rfl⟩ _ hcfix,
        by rw [Subgroup.coe_subtype, actW_apply_coe]⟩
    rw [eq_top_iff]
    intro w _
    obtain ⟨w', hw', hww⟩ := hle w.2
    have e : w' = w := Subtype.ext hww
    rw [← e]
    exact hw'
  have hb₁' : b₁ ∈ P ⊔ T := mem_sup_right hb₁
  have hb₂' : b₂ ∈ P ⊔ T := mem_sup_right hb₂
  rcases class_aut hstr hfix hgen' with ⟨-, h4⟩ | ⟨L₁, L₂, hB⟩
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc4 : Nat.card ↥((T.subgroupOf (P ⊔ T)).map (actW hN)) = 2 ^ 2 := by
      rw [h4]
      norm_num
    have hcomm : IsMulCommutative ↥((T.subgroupOf (P ⊔ T)).map (actW hN)) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq hc4
    have e := hcomm.is_comm.comm
      ⟨actW hN ⟨b₁, hb₁'⟩, ⟨b₁, hb₁'⟩, mem_subgroupOf.2 hb₁, rfl⟩
      ⟨actW hN ⟨b₂, hb₂'⟩, ⟨b₂, hb₂'⟩, mem_subgroupOf.2 hb₂, rfl⟩
    have e' : actW hN ⟨b₁, hb₁'⟩ * actW hN ⟨b₂, hb₂'⟩ =
        actW hN ⟨b₂, hb₂'⟩ * actW hN ⟨b₁, hb₁'⟩ := congrArg Subtype.val e
    have hcW : ⁅b₁, b₂⁆ ∈ centralizer (W : Set G) := by
      have h1 : actW hN ⁅(⟨b₁, hb₁'⟩ : ↥(P ⊔ T)), ⟨b₂, hb₂'⟩⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_def, e']
        group
      have h2 := (actW_eq_one_iff hN _).1 h1
      simpa [commutatorElement_def] using h2
    obtain ⟨y, hy, hny⟩ := hc
    apply hny
    apply hC
    have hcT : ⁅b₁, b₂⁆ ∈ T := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hb₁ hb₂) (inv_mem hb₁)) (inv_mem hb₂)
    refine mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 (hTP hcT) y).1 hy) (inv_mem hy), ?_⟩
    have h5 : y * ⁅b₁, b₂⁆⁻¹ * y⁻¹ ∈ centralizer (W : Set G) :=
      (mem_normalizer_iff.1 (mem_normalizer_centralizer_of (hN (mem_sup_left hy))) _).1
        (inv_mem hcW)
    have e5 : ⁅b₁, b₂⁆ * y * ⁅b₁, b₂⁆⁻¹ * y⁻¹ = ⁅b₁, b₂⁆ * (y * ⁅b₁, b₂⁆⁻¹ * y⁻¹) := by group
    rw [e5]
    exact mul_mem hcW h5
  ·
    have hx₁₂ : actW hN ⟨b₁, hb₁'⟩ * actW hN ⟨b₂, hb₂'⟩ =
        actW hN ⟨b₁ * b₂, mul_mem hb₁' hb₂'⟩ := by
      rw [← map_mul]
      rfl
    refine false_of_blocks hB hstr.tb_le hcard9 hexp3 ⟨⟨b₁, hb₁'⟩, rfl⟩ ⟨⟨b₂, hb₂'⟩, rfl⟩
      (hinv b₁ hb₁' h₁) (hinv b₂ hb₂' h₂) ?_
    rw [hx₁₂]
    exact hinv (b₁ * b₂) (mul_mem hb₁' hb₂') h₁₂

end CFSG.Quasithin.H13.U3
