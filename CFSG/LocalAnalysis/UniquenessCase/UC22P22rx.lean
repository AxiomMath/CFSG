module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ru
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rv
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rw
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open scoped commutatorElement

section Tools

variable {G : Type} [Group G]

theorem uc22p22r_card_sup_of_comm [Finite G] {A B : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAB : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  set f : ↥A × ↥B → G := fun x => (x.1 : G) * x.2 with hf
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [hf] at h
    have h1 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h]
        _ = b' * (b : G)⁻¹ := by group
    have h2 : (a' : G)⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, h1 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at h2
    have ha : a' = a := Subtype.ext h2
    subst ha
    have hb : (b : G) = b' := mul_left_cancel h
    rw [Subtype.ext hb]
  have hrange : Set.range f = ((A ⊔ B : Subgroup G) : Set G) := by
    ext x
    rw [SetLike.mem_coe, uc22p22r_mem_sup_iff hcomm]
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨a, a.2, b, b.2, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩
  calc Nat.card ↥(A ⊔ B) = Nat.card ↑(Set.range f) := by rw [hrange]; rfl
    _ = Nat.card (↥A × ↥B) := Nat.card_range_of_injective hinj
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

theorem uc22p22r_sylow_eq_sup [Finite G] {p : ℕ} [Fact p.Prime] {A B S : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥)
    (hS : CFSG.ABGLocalTools.IsSylowOf p S (A ⊔ B)) : S = (S ⊓ A) ⊔ (S ⊓ B) := by
  have hcomm' : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  have hNA : A ⊔ B ≤ normalizer (A : Set G) := uc22p22r_sup_le_normalizer_left hcomm
  have hNB : A ⊔ B ≤ normalizer (B : Set G) := by
    rw [sup_comm]
    exact uc22p22r_sup_le_normalizer_left hcomm'
  have hSA := hS.inf_of_le_normalizer le_sup_left hNA
  have hSB := hS.inf_of_le_normalizer le_sup_right hNB
  have hc1 : ∀ a ∈ S ⊓ A, ∀ b ∈ S ⊓ B, a * b = b * a := fun a ha b hb => hcomm a ha.2 b hb.2
  have hd1 : (S ⊓ A) ⊓ (S ⊓ B) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ A ⊓ B := ⟨hx.1.2, hx.2.2⟩
    rwa [hAB] at h1
  have hcardS : Nat.card S = Nat.card ↥(S ⊓ A) * Nat.card ↥(S ⊓ B) := by
    rw [hS.card_eq, hSA.card_eq, hSB.card_eq, uc22p22r_card_sup_of_comm hcomm hAB,
      Nat.factorization_mul (Nat.card_pos (α := ↥A)).ne' (Nat.card_pos (α := ↥B)).ne', Finsupp.add_apply,
      pow_add]
  symm
  refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
  rw [uc22p22r_card_sup_of_comm hc1 hd1, hcardS]

theorem uc22p22r_lgConj_normal (L : Subgroup G) : (Ext.lgConj L).Normal := by
  constructor
  intro x hx g
  have h1 : (Ext.lgConj L).map (MulAut.conj g).toMonoidHom ≤ Ext.lgConj L := by
    unfold Ext.lgConj
    rw [Subgroup.map_iSup]
    refine iSup_le fun h => ?_
    rw [uc22p22d_map_conj_map_conj]
    exact le_iSup (fun h' : G => L.map (MulAut.conj h').toMonoidHom) (g * h)
  exact h1 ⟨x, hx, rfl⟩

theorem uc22p22r_isSylowOf_mbarImage [Finite G] {M V P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hP : CFSG.ABGLocalTools.IsSylowOf p P M) : CFSG.ABGLocalTools.IsSylowOf p (mbarImage M V P) ⊤ := by
  obtain ⟨hPM, hPp, hPidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
  refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨le_top, ?_, ?_⟩
  · have h1 : IsPGroup p (P.subgroupOf M) := hPp.comap_subtype
    exact h1.map (QuotientGroup.mk' (kerAct M V).normalCore)
  · rw [Subgroup.relIndex_top_right]
    have hdvd : (mbarImage M V P).index ∣ (P.subgroupOf M).index :=
      Subgroup.index_map_dvd (P.subgroupOf M) (QuotientGroup.mk'_surjective _)
    intro hd
    exact hPidx (hd.trans hdvd)

end Tools

section Shapes

variable {H : Type} [Group H] [Finite H] {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod] [Finite Vmod]
  (ρ : Representation (ZMod 2) H Vmod)

theorem uc22p22r_shape_facts (hfaith : Function.Injective ρ) {L : Subgroup H} {t : H} {n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) (hn : 3 ≤ n) (hL : IsL2 ↥L n)
    (hcomm : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj t).toMonoidHom, a * b = b * a)
    (hsh : NatOmegaPlus4 ρ (L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊤ ⊥ n ∨
      (commOn ρ L ⊤ ⊔ commOn ρ (L.map (MulAut.conj t).toMonoidHom) ⊤ = ⊤ ∧
        commOn ρ L ⊤ ⊓ commOn ρ (L.map (MulAut.conj t).toMonoidHom) ⊤ = ⊥ ∧
        (NatL2 ρ L (commOn ρ L ⊤) ⊥ n ∨
          (∃ k : ℕ, n = 2 * k ∧
            (SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 1 (commOn ρ L ⊤) ⊥ ∨
              SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 2 (commOn ρ L ⊤) ⊥)) ∨
          (n = 3 ∧ SecIrr ρ L (commOn ρ L ⊤) ⊥ 8)))) :
    ∃ Y : Submodule (ZMod 2) Vmod, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (normalizer (L : Set H)) Y ∧
      (∀ c ∈ centralizer ((L ⊔ L.map (MulAut.conj t).toMonoidHom : Subgroup H) : Set H),
        (∃ k : ℕ, c ^ (p ^ k) = 1) → c = 1) ∧
      ∀ S : Subgroup H, CFSG.ABGLocalTools.IsSylowOf 2 S
        ((L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊔
          centralizer ((L ⊔ L.map (MulAut.conj t).toMonoidHom : Subgroup H) : Set H)) →
        ¬ Nat.card ↥(fixOn ρ S Y) ≡ 1 [MOD p] := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Lt := L.map (MulAut.conj t).toMonoidHom with hLt
  set X := L ⊔ Lt with hX
  set C := centralizer (X : Set H) with hC
  have hZL := uc22p22g_center_bot hL
  rcases hsh with hO | ⟨hsum, -, hmod⟩
  · refine ⟨⊤, fun _ _ _ _ => Submodule.mem_top, fun c hc hk => ?_, fun S hS => ?_⟩
    · obtain ⟨k, hk⟩ := hk
      exact uc22p22r_F1_omegaPlus ρ hfaith hp hp2 hpn hn hO hc hk
    · exact uc22p22r_F2_omegaPlus ρ hfaith hp hp2 hpn hn hO hS
  set W := commOn ρ L ⊤ with hW
  set W' := commOn ρ Lt ⊤ with hW'
  have hF1W : ∀ c ∈ centralizer (L : Set H), ∀ k : ℕ, c ^ (p ^ k) = 1 → ∀ w ∈ W, ρ c w = w := by
    intro c hc k hk
    rcases hmod with hnat | ⟨k', hk', hmods⟩ | ⟨h3, h8⟩
    · exact uc22p22r_F1W_natL2 ρ hp hp2 hpn hnat hc hk
    · have hpk : (2 : ℤ) ^ (2 * k') ≡ -1 [ZMOD (p : ℤ)] := by
        rw [← hk']
        exact hpn
      exact uc22p22r_F1W_omegaMinus ρ hp hp2 hpk hmods hc hk
    · have hL3 : IsL2 ↥L 3 := h3 ▸ hL
      exact uc22p22r_F1W_rank8 ρ hL3 h8 hc
  have hF2W : ∀ U S₂ : Subgroup H, CFSG.ABGLocalTools.IsSylowOf 2 U L → S₂ ≤ centralizer (L : Set H) →
      IsPGroup 2 ↥S₂ → ¬ Nat.card ↥(fixOn ρ (U ⊔ S₂) W) ≡ 1 [MOD p] := by
    intro U S₂ hU hS₂ hS₂2
    rcases hmod with hnat | ⟨k', hk', hmods⟩ | ⟨h3, h8⟩
    · exact uc22p22r_F2W_natL2 ρ hp hp2 hpn hL hnat hU hS₂ hS₂2
    · have hpk : (2 : ℤ) ^ (2 * k') ≡ -1 [ZMOD (p : ℤ)] := by
        rw [← hk']
        exact hpn
      have hLk : IsL2 ↥L (2 * k') := hk' ▸ hL
      exact uc22p22r_F2W_omegaMinus ρ hp hp2 hpk hLk hmods hU hS₂ hS₂2
    · have hL3 : IsL2 ↥L 3 := h3 ▸ hL
      have hp3 : p = 3 := by
        have h1 : (p : ℤ) ∣ -1 - 2 ^ n := Int.modEq_iff_dvd.1 hpn
        rw [h3] at h1
        have h2 : (p : ℤ) ∣ ((9 : ℕ) : ℤ) := by
          have e : ((9 : ℕ) : ℤ) = -(-1 - 2 ^ 3) := by norm_num
          rw [e]
          exact h1.neg_right
        have h4 : p ∣ 3 ^ 2 := by simpa using Int.natCast_dvd_natCast.1 h2
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h4)
      rw [hp3]
      exact uc22p22r_F2W_rank8 ρ hL3 h8 hU hS₂
  refine ⟨W, ?_, ?_, ?_⟩
  · intro g hg w hw
    have h1 := uc22p22d_apply_commOn_le ρ L g hw
    have hgL : L.map (MulAut.conj g).toMonoidHom = L := Subgroup.mem_normalizer_iff_map_conj_eq.1 hg
    rwa [hgL] at h1
  · rintro c hc ⟨k, hk⟩
    have hcL : c ∈ centralizer (L : Set H) := Subgroup.centralizer_le (le_sup_left : L ≤ X) hc
    have hcW := hF1W c hcL k hk
    have hc' : t⁻¹ * c * t ∈ centralizer (L : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlt : t * l * t⁻¹ ∈ X := le_sup_right (a := L) ⟨l, hl, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.1 hc _ hlt
      calc l * (t⁻¹ * c * t) = t⁻¹ * (t * l * t⁻¹ * c) * t := by group
        _ = t⁻¹ * (c * (t * l * t⁻¹)) * t := by rw [h1]
        _ = t⁻¹ * c * t * l := by group
    have hc'k : (t⁻¹ * c * t) ^ (p ^ k) = 1 := by
      have e : t⁻¹ * c * t = MulAut.conj t⁻¹ c := by simp [MulAut.conj_apply]
      rw [e, ← map_pow, hk, map_one]
    have hc'W := hF1W _ hc' k hc'k
    have hcW' : ∀ w ∈ W', ρ c w = w := by
      intro w hw
      have h1 := uc22p22d_apply_commOn_le ρ Lt t⁻¹ hw
      rw [hLt, uc22p22d_map_conj_map_conj, inv_mul_cancel, uc22p22r_map_conj_one] at h1
      have h2 := hc'W _ h1
      have e : c = t * (t⁻¹ * c * t) * t⁻¹ := by group
      calc ρ c w = ρ (t * (t⁻¹ * c * t) * t⁻¹) w := by rw [← e]
        _ = ρ t (ρ (t⁻¹ * c * t) (ρ t⁻¹ w)) := by simp only [map_mul, Module.End.mul_apply]
        _ = ρ t (ρ t⁻¹ w) := by rw [h2]
        _ = w := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    apply hfaith
    rw [map_one]
    apply LinearMap.ext
    intro x
    have hx : x ∈ W ⊔ W' := hsum ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, hcW y hy, hcW' z hz, Module.End.one_apply]
  · intro S hS
    set B := Lt ⊔ C with hB
    have hBL : B ≤ centralizer (L : Set H) := by
      refine sup_le ?_ (Subgroup.centralizer_le (le_sup_left : L ≤ X))
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact hcomm l hl b hb
    have hcommLB : ∀ a ∈ L, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
      Subgroup.mem_centralizer_iff.1 (hBL hb) a ha
    have hLB : L ⊓ B = ⊥ := uc22p22r_inf_eq_bot_of_comm hcommLB hZL
    have hsup : L ⊔ B = X ⊔ C := by rw [hB, ← sup_assoc]
    have hS' : CFSG.ABGLocalTools.IsSylowOf 2 S (L ⊔ B) := by
      rw [hsup]
      exact hS
    have hdec := uc22p22r_sylow_eq_sup hcommLB hLB hS'
    have hU : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ L) L :=
      hS'.inf_of_le_normalizer le_sup_left (uc22p22r_sup_le_normalizer_left hcommLB)
    have hS₂ : S ⊓ B ≤ centralizer (L : Set H) := inf_le_right.trans hBL
    have hS₂2 : IsPGroup 2 ↥(S ⊓ B) := hS.isPGroup.to_le inf_le_left
    rw [hdec]
    exact hF2W _ _ hU hS₂ hS₂2

end Shapes

end CFSG.LocalAnalysis.UniquenessCase.UC22
