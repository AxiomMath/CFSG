module

public import CFSG.Quasithin.H13.A6S13833a
public import CFSG.Quasithin.H13.A6S13834Q

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

@[expose] def cyc4List : List (Perm (Fin 6)) :=
  [swap 1 2 * swap 2 3, swap 0 2 * swap 2 3, swap 0 1 * swap 1 3, swap 0 1 * swap 1 2]

theorem cyc4_facts : ∀ σ ∈ cyc4List,
    Perm.sign σ = 1 ∧ σ 4 = 4 ∧ σ 5 = 5 ∧ σ ^ 3 = 1 ∧ σ ≠ 1 := by
  decide +kernel

theorem fix_cyc4 : ∀ x : P6, InW4 x → ¬ InW3 x → ∃ σ ∈ cyc4List, act4f σ x = x := by
  decide +kernel

@[expose] def a4FixList : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2,
    swap 1 2 * swap 2 3, swap 0 2 * swap 2 3, swap 0 1 * swap 1 3, swap 0 1 * swap 1 2,
    (swap 1 2 * swap 2 3) ^ 2, (swap 0 2 * swap 2 3) ^ 2, (swap 0 1 * swap 1 3) ^ 2,
    (swap 0 1 * swap 1 2) ^ 2]

theorem a4Fix_facts : ∀ σ ∈ a4FixList, Perm.sign σ = 1 ∧ σ 4 = 4 ∧ σ 5 = 5 := by
  decide +kernel

@[expose] def TransW3At (x x' : P6) : Prop :=
  InW4 x → InW3 x → x ≠ 1 → x ≠ e0123 → InW4 x' → InW3 x' → x' ≠ 1 → x' ≠ e0123 →
    ∃ σ ∈ a4FixList, act4f σ x = x'

instance (x x' : P6) : Decidable (TransW3At x x') := by unfold TransW3At; infer_instance

theorem trans_W3 : ∀ x x' : P6, TransW3At x x' := by
  decide +kernel

theorem inW3_inv : ∀ σ : Perm (Fin 6), InW3 (act4f σ⁻¹ e0123) → InW3 (act4f σ e0123) := by
  decide +kernel

theorem card_evenWeight6 : Nat.card ↥(evenWeight 6) = 32 := by
  have h : Nat.card ↥(evenWeight 6) = Nat.card {x : Fin 6 → ZMod 2 // ∑ i, x i = 0} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun x => by simp [evenWeight, AddMonoidHom.mem_ker])
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem card_constWeight6 : Nat.card ↥(constWeight 6) = 2 := by
  have h : Nat.card ↥(constWeight 6) =
      Nat.card {v : Fin 6 → ZMod 2 // ∑ i, v i = 0 ∧ ∀ i j, v i = v j} := by
    apply Nat.card_congr
    exact { toFun := fun x => ⟨((x : ↥(evenWeight 6)) : Fin 6 → ZMod 2), sum_eq_zero _, x.2⟩
            invFun := fun v => ⟨⟨v.1, mem_ev_of_sum_zero v.2.1⟩, v.2.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem card_altHeart6 : Nat.card (AltHeart 6) = 16 := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (constWeight 6)
  rw [card_evenWeight6, card_constWeight6] at h
  show Nat.card (↥(evenWeight 6) ⧸ constWeight 6) = 16
  omega

theorem cList_fpf : ∀ σ ∈ cList, σ ^ 3 = 1 → σ ≠ 1 → ∀ i : Fin 6, σ i ≠ i := by
  decide +kernel

theorem fpf3_fix : ∀ σ : Perm (Fin 6), σ ^ 3 = 1 → (∀ i, σ i ≠ i) → ∀ w : Fin 6 → ZMod 2,
    ∑ i, w i = 0 → (vp σ w = w ∨ vp σ w = w + onesV) → w = 0 ∨ w = onesV := by
  decide +kernel

theorem e0_of_inv : ∀ σ ∈ cList, σ ^ 3 = 1 → σ ≠ 1 → ∀ a ∈ e8List, a ≠ 1 → a ≠ iota0 →
    ∀ e ∈ e0List, e ∈ [1, a, σ * a * σ⁻¹, σ * (σ * a * σ⁻¹) * σ⁻¹, a * (σ * a * σ⁻¹),
      a * (σ * (σ * a * σ⁻¹) * σ⁻¹), (σ * a * σ⁻¹) * (σ * (σ * a * σ⁻¹) * σ⁻¹)] := by
  decide +kernel


namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section E0

variable (hNS : ¬ LieModel G .PSp 3 2 1)
  (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz) (h13314 : Stmt13_3_14)
  (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) {K : Subgroup G} (hKT : K ⊔ T = S.G1)
  {ρ' : ↥S.G1 →* Perm (Fin 6)}
  (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (hker' : ∀ h : ↥S.G1, ρ' h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
  (hKA' : ∀ k : ↥S.G1, (k : G) ∈ K → ρ' k ∈ alternatingGroup (Fin 6))
  (honto' : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ)
include hNS h13315 h1356two hG1 h13314 hF hKT hN' hker' hKA' honto'

theorem not_O2_le_of_quad {B : Subgroup G} (hBH : B ≤ S.G1)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBV : ∀ b ∈ B, ∀ y ∈ conjClosure V S.G1, b * y * b⁻¹ * y⁻¹ ∈ B) :
    ¬ pCoreOf 2 (S.L1 ⊔ pCoreOf 2 S.G1) ≤ B ⊔ pCoreOf 2 S.G1 := by
  set Q := pCoreOf 2 S.G1 with hQdef
  have hL1H : S.L1 ≤ S.G1 := le_sup_left.trans hF.toHypF91.L₁T_le_H
  have hQT : Q ≤ T := isSylowTwoOf_pCoreOf_le hF.toHypF91.sylow_H
  have hT8' : 8 ∣ Nat.card ((T.subgroupOf S.G1).map ρ') :=
    eight_dvd_card_map hF.toHypF91.sylow_H ρ' (fun h h1 => hQT ((hker' h).1 h1))
      fun σ hσ => (honto' σ hσ).elim fun k hk => ⟨k, hk.2⟩
  intro hcon
  obtain ⟨l₁, hl₁, he₁⟩ := S.exists_L1_E0 hN' hker' hL1H hT8' _ cert_pts.2.2.1
  obtain ⟨l₂, hl₂, he₂⟩ := S.exists_L1_E0 hN' hker' hL1H hT8' _ cert_pts.2.2.2.1
  have hO₁ := S.mem_O2_of_E0 hN' hker' hL1H (Subgroup.mem_sup_left hl₁)
    (by rw [he₁]; exact cert_pts.2.2.1)
  have hO₂ := S.mem_O2_of_E0 hN' hker' hL1H (Subgroup.mem_sup_left hl₂)
    (by rw [he₂]; exact cert_pts.2.2.2.1)
  have himg : ∀ l : ↥S.G1, (l : G) ∈ B ⊔ Q → ∃ b : ↥S.G1, (b : G) ∈ B ∧ ρ' b = ρ' l := by
    intro l hl
    have hle : B ⊔ Q ≤ preImg ρ' ((B.subgroupOf S.G1).map ρ') := by
      refine sup_le (fun b hb => mem_preImg.2 ⟨hBH hb,
        ⟨⟨b, hBH hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩⟩) fun q hq =>
        mem_preImg.2 ⟨pCoreOf_le 2 S.G1 hq, ?_⟩
      rw [(hker' _).2 hq]
      exact Subgroup.one_mem _
    obtain ⟨_, ⟨b, hb, hbl⟩⟩ := mem_preImg.1 (hle hl)
    exact ⟨b, Subgroup.mem_subgroupOf.mp hb, hbl⟩
  obtain ⟨b₁, hb₁, hb₁e⟩ := himg l₁ (hcon hO₁)
  obtain ⟨b₂, hb₂, hb₂e⟩ := himg l₂ (hcon hO₂)
  obtain ⟨x, -, hx⟩ := honto' _ (Equiv.Perm.mem_alternatingGroup.mpr cert_pts.1)
  obtain ⟨v₀, hv₀, hv₀3⟩ := S.exists_V_not_V3
  have hxv := S.fix_of_cert hN' h13315 hv₀ hv₀3 hF.F911_2 hF.toHypF91.elemAbelian hBc hBV
    hb₁ hb₂ hx (by rw [hb₁e, he₁]) (by rw [hb₂e, he₂])
  have hall := S.fix_all hN' h13315 hv₀ hv₀3 hKT honto' hKA' hker' hQT hx hxv
  exact S.false_of_fix h13315 hv₀ hv₀3 hNS h1356two hG1 h13314 hF.toHypF91.V_le_H hall

end E0

section NatFpf

variable {ρ ρ' : ↥S.G1 →* Perm (Fin 6)} {τ : Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
  (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (hker' : ∀ h : ↥S.G1, ρ' h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (AltHeart 6)}
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
      (QuotientAddGroup.mk (permWeight 6 (ρ h) x) : AltHeart 6) = Multiplicative.toAdd (β v))
include hρ' hN' hker' hβk hβe

theorem mem_V1_of_fpf_nat {k : ↥S.G1} (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1)
    (hkN : (k : G) ∈ Subgroup.normalizer (S.V3 : Set G)) {u : G}
    (hu : u ∈ conjClosure S.V3 S.G1) (hku : (k : G) * u * (k : G)⁻¹ * u⁻¹ ∈ fsuV1 T V) :
    u ∈ fsuV1 T V := by
  have hc := (hN' k).2 hkN
  have h3' : ρ' k ^ 3 = 1 := by rw [← map_pow, hk3, map_one]
  have h1' : ρ' k ≠ 1 := S.rho_ne_one_of_cube hker' hk3 hk1
  have hfp' := cList_fpf _ hc h3' h1'
  have h3 : ρ k ^ 3 = 1 := by rw [← map_pow, hk3, map_one]
  have hfp : ∀ i, ρ k i ≠ i := by
    intro i h
    apply hfp' (τ⁻¹ i)
    have e : ρ' k = τ⁻¹ * ρ k * τ := hρ' k
    rw [e]
    simp [Perm.mul_apply, h]
  have hUN : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 S.G1 :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 k.2) u).mp hu
  have hβ : β ⟨_, hUN⟩ = β ⟨u, hu⟩ := by
    have h1 : β ⟨(k : G) * u * (k : G)⁻¹ * u⁻¹,
        (conjClosure S.V3 S.G1).mul_mem hUN ((conjClosure S.V3 S.G1).inv_mem hu)⟩ = 1 :=
      (hβk _).2 hku
    have e : (⟨_, hUN⟩ : ↥(conjClosure S.V3 S.G1)) = ⟨(k : G) * u * (k : G)⁻¹ * u⁻¹,
        (conjClosure S.V3 S.G1).mul_mem hUN ((conjClosure S.V3 S.G1).inv_mem hu)⟩ * ⟨u, hu⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    rw [e, map_mul, h1, one_mul]
  obtain ⟨r, hr0⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β ⟨u, hu⟩))
  have he := hβe k ⟨u, hu⟩ ⟨_, hUN⟩ rfl r hr0
  rw [hβ, ← hr0, mk_eq_mk_iff] at he
  have hw := fpf3_fix _ h3 hfp (r : Fin 6 → ZMod 2) (sum_eq_zero r) he
  have hz : (QuotientAddGroup.mk r : AltHeart 6) = 0 := (mk_eq_zero_iff r).2 hw
  rw [hr0] at hz
  exact (hβk _).1 (Multiplicative.toAdd.injective (by rw [hz, toAdd_one]))

theorem mem_V3_of_fpf_nat {k : ↥S.G1} (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1)
    (hkN : (k : G) ∈ Subgroup.normalizer (S.V3 : Set G)) {u : G}
    (hu : u ∈ conjClosure S.V3 S.G1) (hku : u⁻¹ * ((k : G) * u * (k : G)⁻¹) ∈ S.V3) :
    u ∈ S.V3 := by
  have hk3' : (k : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hk3
  have h8 : ¬ 3 ∣ Nat.card ↥S.V3 := by rw [S.card_V3]; norm_num
  obtain ⟨n, hn, hkn⟩ := exists_comm_mul_of_conj_mem hk3' h8
    (fun n hn => (Subgroup.mem_normalizer_iff.mp hkN n).mp hn) hku
  have hun : u * n ∈ conjClosure S.V3 S.G1 :=
    (conjClosure S.V3 S.G1).mul_mem hu (le_conjClosure S.V3 S.G1 hn)
  have h1 : (k : G) * (u * n) * (k : G)⁻¹ * (u * n)⁻¹ ∈ fsuV1 T V := by
    rw [hkn, mul_inv_cancel]; exact Subgroup.one_mem _
  have h2 := S.mem_V1_of_fpf_nat hρ' hN' hker' hβk hβe hk3 hk1 hkN hun h1
  have e : u = (u * n) * n⁻¹ := by group
  rw [e]
  exact S.V3.mul_mem (S.V1_le_V3 h2) (S.V3.inv_mem hn)

end NatFpf

section NatConj

theorem exists_L1_cube_fix (hhat : ¬ IsHatA6 L) {y : G}
    (hy : y ∈ V) (hy3 : y ∉ S.V3) : ∃ c ∈ S.L1, c ^ 3 = 1 ∧ c ≠ 1 ∧ c * y * c⁻¹ = y := by
  have hx4 : InW4 ((S.frame.ψ ⟨y, hy⟩ : ↥W4) : P6) := (S.frame.ψ ⟨y, hy⟩).2
  have hx3 : ¬ InW3 ((S.frame.ψ ⟨y, hy⟩ : ↥W4) : P6) := fun h =>
    hy3 (S.mem_pre.2 ⟨hy, h⟩)
  obtain ⟨σ, hσ, hσx⟩ := fix_cyc4 _ hx4 hx3
  obtain ⟨hs, h4, h5, h3, h1⟩ := cyc4_facts σ hσ
  obtain ⟨g, hgL1, hg⟩ := S.exists_L1_of_three hs h4 h5 h3
  have hgL : (g : G) ∈ L := (S.L1_le hgL1).1
  have hg3C : ((g ^ 3 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
      Subgroup.centralizer (V : Set G) :=
    (S.rho_eq_one_iff _).1 (by rw [map_pow, hg, h3])
  have hg3O : (g : G) ^ 3 ∈ pCoreOf 2 L :=
    S.inf_centralizer_le_pCoreOf hhat ⟨L.pow_mem hgL 3, by simpa using hg3C⟩
  obtain ⟨n, hn⟩ := pCoreOf_isPGroup (r := 2) L ⟨_, hg3O⟩
  have hn' : ((g : G) ^ 3) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hσo : orderOf σ = 3 := orderOf_eq_prime h3 h1
  have hσn : σ ^ (2 ^ n) ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hσo] at hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have hfix : ∀ m : ℕ, act4f (σ ^ m) ((S.frame.ψ ⟨y, hy⟩ : ↥W4) : P6) =
      ((S.frame.ψ ⟨y, hy⟩ : ↥W4) : P6) := by
    intro m
    induction m with
    | zero => exact act4f_one _ (S.frame.ψ ⟨y, hy⟩).2
    | succ m ih => rw [pow_succ, act4f_mul, hσx, ih]
  refine ⟨(g : G) ^ (2 ^ n), S.L1.pow_mem hgL1 _, ?_, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hn']
  · intro h
    apply hσn
    have e : g ^ (2 ^ n) = 1 := Subtype.ext (by simpa using h)
    rw [← hg, ← map_pow, e, map_one]
  · have := (S.conj_eq_iff (g ^ (2 ^ n)) ⟨y, hy⟩).2 (by
      rw [map_pow, hg]
      exact Subtype.ext (hfix _))
    simpa using this

variable (hNS : ¬ LieModel G .PSp 3 2 1)
  (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz) (h13314 : Stmt13_3_14)
  (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) (hhat : ¬ IsHatA6 L)
  {K : Subgroup G} (hKT : K ⊔ T = S.G1)
  {ρ ρ' : ↥S.G1 →* Perm (Fin 6)} {τ : Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
  (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (hker' : ∀ h : ↥S.G1, ρ' h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
  (hKA' : ∀ k : ↥S.G1, (k : G) ∈ K → ρ' k ∈ alternatingGroup (Fin 6))
  (honto' : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ)
  (hE8 : ∀ y : ↥S.G1, (y : G) ∈ pCoreOf 2 (S.L1 ⊔ T) → ρ' y ∈ e8List)
  (hE0 : ∀ y : G, y ∈ pCoreOf 2 (S.L1 ⊔ pCoreOf 2 S.G1) → ∃ hy : y ∈ S.G1, ρ' ⟨y, hy⟩ ∈ e0List)
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (AltHeart 6)} (hβs : Function.Surjective β)
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
      (QuotientAddGroup.mk (permWeight 6 (ρ h) x) : AltHeart 6) = Multiplicative.toAdd (β v))

include hβs hβk in
theorem card_UH_nat : Nat.card ↥(conjClosure S.V3 S.G1) = 32 := by
  have hk : β.ker = (fsuV1 T V).subgroupOf (conjClosure S.V3 S.G1) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk u
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
  have h2 : Nat.card (↥(conjClosure S.V3 S.G1) ⧸ β.ker) = 16 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (AltHeart 6) ≃ AltHeart 6),
      card_altHeart6]
  have h3 : Nat.card ↥β.ker = 2 := by
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (S.V1_le_V3.trans (le_conjClosure S.V3 S.G1))).toEquiv, S.card_V1]
  rw [h1, h2, h3]


include hNS h13315 h1356two hG1 h13314 hF hhat hKT hρ' hN' hker' hKA' honto' hE8 hE0 hβs hβk hβe

theorem conj_UH_le_QH_nat {l : G} (hl : l ∈ L) (hz : l * S.z * l⁻¹ ∉ S.V3) :
    conjSub l (conjClosure S.V3 S.G1) ≤ pCoreOf 2 S.G1 := by
  set Q := pCoreOf 2 S.G1 with hQdef
  set U := conjClosure S.V3 S.G1 with hUdef
  set B := conjSub l U with hBdef
  set y := l * S.z * l⁻¹ with hydef
  have hlN : l ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hl
  have hyV : y ∈ V := (Subgroup.mem_normalizer_iff.mp hlN S.z).mp S.z_mem_V
  have hL1H : S.L1 ≤ S.G1 := le_sup_left.trans hF.toHypF91.L₁T_le_H
  have hTH : T ≤ S.G1 := hKT ▸ le_sup_right
  obtain ⟨c, hcL1, hc3, hc1, hcy⟩ := S.exists_L1_cube_fix hhat hyV hz
  have hcH : c ∈ S.G1 := hL1H hcL1
  have hcL : c ∈ L := (S.L1_le hcL1).1
  set k := l⁻¹ * c * l with hkdef
  have hkz : k * S.z * k⁻¹ = S.z := by
    have e : k * S.z * k⁻¹ = l⁻¹ * (c * y * c⁻¹) * l := by rw [hkdef, hydef]; group
    rw [e, hcy, hydef]; group
  have hkH : k ∈ S.G1 := by
    show k ∈ Subgroup.centralizer ({S.z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k * S.z = k * S.z * k⁻¹ * k := by group
      _ = S.z * k := by rw [hkz]
  have hkL : k ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) hcL) hl
  have hkV1 : k ∈ Subgroup.normalizer (fsuV1 T V : Set G) := by rw [S.normalizer_V1]; exact hkH
  have hkN3 : k ∈ Subgroup.normalizer (S.V3 : Set G) := S.NLV1_le_NV3 ⟨hkL, hkV1⟩
  have hk3 : (⟨k, hkH⟩ : ↥S.G1) ^ 3 = 1 := Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    have e : (l⁻¹ * c * l) ^ 3 = l⁻¹ * c ^ 3 * l := by
      simp only [pow_succ, pow_zero, one_mul]; group
    rw [hkdef, e, hc3]; group)
  have hk1 : (⟨k, hkH⟩ : ↥S.G1) ≠ 1 := by
    intro h
    apply hc1
    have h' : k = 1 := congrArg Subtype.val h
    calc c = l * k * l⁻¹ := by rw [hkdef]; group
      _ = 1 := by rw [h']; group
  have hfpf : ∀ b ∈ B, b⁻¹ * (c * b * c⁻¹) ∈ conjSub l S.V3 → b ∈ conjSub l S.V3 := by
    intro b hb hbc
    have hu : l⁻¹ * b * l ∈ U := by simpa using mem_conjSub.mp hb
    have hu' : (l⁻¹ * b * l)⁻¹ * (k * (l⁻¹ * b * l) * k⁻¹) ∈ S.V3 := by
      have := mem_conjSub.mp hbc
      rw [hkdef]
      convert this using 1
      group
    have h := S.mem_V3_of_fpf_nat hρ' hN' hker' hβk hβe hk3 hk1 hkN3 hu hu'
    rw [mem_conjSub]
    simpa using h
  have hCyB : ∀ w : G, w * y * w⁻¹ = y → ∀ b ∈ B, w * b * w⁻¹ ∈ B := by
    intro w hw b hb
    have hw' : l⁻¹ * w * l ∈ S.G1 := by
      show l⁻¹ * w * l ∈ Subgroup.centralizer ({S.z} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e : l⁻¹ * w * l * S.z * (l⁻¹ * w * l)⁻¹ = l⁻¹ * (w * y * w⁻¹) * l := by
        rw [hydef]; group
      calc l⁻¹ * w * l * S.z = l⁻¹ * w * l * S.z * (l⁻¹ * w * l)⁻¹ * (l⁻¹ * w * l) := by group
        _ = S.z * (l⁻¹ * w * l) := by rw [e, hw, hydef]; group
    have hu : l⁻¹ * b * l ∈ U := by simpa using mem_conjSub.mp hb
    have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hw')
      _).mp hu
    rw [mem_conjSub]
    convert h2 using 1
    group
  have hcB : ∀ b ∈ B, c * b * c⁻¹ ∈ B := hCyB c hcy
  have hBV : ∀ b ∈ B, ∀ w ∈ conjClosure V S.G1, b * w * b⁻¹ * w⁻¹ ∈ B := by
    intro b hb w hw
    have hwy : w * y * w⁻¹ = y := by
      have := isElemAbelian_comm hF.F911_2 hw (le_conjClosure V S.G1 hyV)
      rw [this]; group
    have h := hCyB w hwy _ (B.inv_mem hb)
    have e : b * w * b⁻¹ * w⁻¹ = b * (w * b⁻¹ * w⁻¹) := by group
    rw [e]
    exact B.mul_mem hb h
  have hBUL : B ≤ conjClosure U L := fun x hx => HypF91.conjSub_le_conjClosure hl hx
  have hULQ := S.UL_le_Q hNS h13315 h1356two hG1 hF
  have hQLT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_le_of_sylow S.h13.sylow le_sup_right
  have hBH : B ≤ S.G1 := hBUL.trans (hULQ.trans (hQLT.trans hTH))
  have hQO : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (S.L1 ⊔ T) := by
    refine le_pCoreOf_of_le_normalizer 2 (hQLT.trans le_sup_right) ?_ (pCoreOf_isPGroup 2 _)
    refine sup_le (fun x hx => le_normalizer_pCoreOf 2 (L ⊔ T)
      (Subgroup.mem_sup_left (S.L1_le hx).1)) fun x hx => le_normalizer_pCoreOf 2 (L ⊔ T)
      (Subgroup.mem_sup_right hx)
  have hBO : B ≤ pCoreOf 2 (S.L1 ⊔ T) := hBUL.trans (hULQ.trans hQO)
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    isElemAbelian_comm (isElemAbelian_conjSub hF.F911_3) ha hb
  set fB : ↥B →* Perm (Fin 6) := ρ'.comp (Subgroup.inclusion hBH) with hfB
  have hfBe : ∀ w : ↥B, fB w = ρ' ⟨(w : G), hBH w.2⟩ := fun w => rfl
  have hrange : fB.range ≤ e8Sub := by
    rintro _ ⟨b, rfl⟩
    exact hE8 _ (hBO b.2)
  have hdvd : Nat.card fB.range ∣ 8 := card_e8Sub ▸ Subgroup.card_dvd_of_le hrange
  have hcard : Nat.card fB.range = (B ⊓ Q).relIndex B := S.card_range_eq hker' hBH
  have hcN3 : c ∈ Subgroup.normalizer (S.V3 : Set G) :=
    S.L1T_le_NV3 (Subgroup.mem_sup_left hcL1)
  have hcc : ρ' ⟨c, hcH⟩ ∈ cList := (hN' _).2 hcN3
  have hc3' : (⟨c, hcH⟩ : ↥S.G1) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hc1' : (⟨c, hcH⟩ : ↥S.G1) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hσ3 : ρ' ⟨c, hcH⟩ ^ 3 = 1 := by rw [← map_pow, hc3', map_one]
  have hσ1 : ρ' ⟨c, hcH⟩ ≠ 1 := S.rho_ne_one_of_cube hker' hc3' hc1'
  have hrinv : ∀ a ∈ fB.range, ρ' ⟨c, hcH⟩ * a * (ρ' ⟨c, hcH⟩)⁻¹ ∈ fB.range := by
    rintro _ ⟨b, rfl⟩
    refine ⟨⟨c * b * c⁻¹, hcB b b.2⟩, ?_⟩
    rw [hfBe, hfBe, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hnot4 : ¬ 4 ≤ Nat.card fB.range := by
    intro h4
    obtain ⟨a, ha, ha1, hai⟩ : ∃ a ∈ fB.range, a ≠ 1 ∧ a ≠ iota0 := by
      by_contra hcon
      push Not at hcon
      have hle : fB.range ≤ Subgroup.zpowers iota0 := fun a ha => by
        by_cases h1 : a = 1
        · rw [h1]; exact Subgroup.one_mem _
        · rw [hcon a ha h1]; exact Subgroup.mem_zpowers _
      have h1 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers] at h1
      have h2 : orderOf iota0 ∣ 2 := orderOf_dvd_of_pow_eq_one (by decide)
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    have ha8 : a ∈ e8List := hrange ha
    have hmem := e0_of_inv _ hcc hσ3 hσ1 a ha8 ha1 hai
    have hb1 := hrinv a ha
    have hb2 := hrinv _ hb1
    apply S.not_O2_le_of_quad hNS h13315 h1356two hG1 h13314 hF hKT hN' hker' hKA' honto'
      hBH hBc hBV
    intro w hw
    obtain ⟨hwH, hwe⟩ := hE0 w hw
    have hwr : ρ' ⟨w, hwH⟩ ∈ fB.range := by
      have h := hmem _ hwe
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h <;> rw [h]
      · exact Subgroup.one_mem _
      · exact ha
      · exact hb1
      · exact hb2
      · exact Subgroup.mul_mem _ ha hb1
      · exact Subgroup.mul_mem _ ha hb2
      · exact Subgroup.mul_mem _ hb1 hb2
    obtain ⟨b, hb⟩ := hwr
    have hq : ((⟨(b : G), hBH b.2⟩ : ↥S.G1)⁻¹ * ⟨w, hwH⟩ : ↥S.G1) ∈ Q.subgroupOf S.G1 := by
      rw [Subgroup.mem_subgroupOf]
      exact (hker' _).1 (by rw [map_mul, map_inv, ← hfBe, hb, inv_mul_cancel])
    rw [Subgroup.mem_subgroupOf] at hq
    have e : w = (b : G) * ((b : G)⁻¹ * w) := by group
    rw [e]
    exact (B ⊔ Q).mul_mem (Subgroup.mem_sup_left b.2)
      (Subgroup.mem_sup_right (by simpa using hq))
  have hnot2 : Nat.card fB.range ≠ 2 := by
    intro h2
    rw [hcard] at h2
    have hV3B : conjSub l S.V3 ≤ B ⊓ Q := le_inf (conjSub_mono l (le_conjClosure S.V3 S.G1))
      (by
        intro x hx
        have h1 : l⁻¹ * x * l ∈ V := S.V3_le_V (by simpa using mem_conjSub.mp hx)
        have h2 : x ∈ V := by
          have := (Subgroup.mem_normalizer_iff.mp hlN (l⁻¹ * x * l)).mp h1
          simpa [mul_assoc] using this
        exact S.V_le_QH hNS h13315 h1356two hG1 hF.F911_3 h2)
    have hcB32 : Nat.card B = 32 := (CosetGeom.card_conjSub _ _).trans (S.card_UH_nat hβs hβk)
    have hcV3 : Nat.card ↥(conjSub l S.V3) = 8 := (CosetGeom.card_conjSub _ _).trans S.card_V3
    have r1 := Subgroup.relIndex_mul_card (B ⊓ Q) B
    rw [inf_eq_left.2 (inf_le_left : B ⊓ Q ≤ B), h2, hcB32] at r1
    have r2 := Subgroup.relIndex_mul_card (conjSub l S.V3) (B ⊓ Q)
    rw [inf_eq_left.2 hV3B, hcV3] at r2
    have hBQ : Nat.card ↥(B ⊓ Q) = 16 := by omega
    rw [hBQ] at r2
    have hrel : (conjSub l S.V3).relIndex (B ⊓ Q) = 2 := by omega
    have hcQ : c ∈ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 S.G1 hcH
    have hcV3 : ∀ x ∈ conjSub l S.V3, c * x * c⁻¹ ∈ conjSub l S.V3 := by
      intro x hx
      have h1 : l⁻¹ * x * l ∈ S.V3 := by simpa using mem_conjSub.mp hx
      have h2 := (Subgroup.mem_normalizer_iff.mp hkN3 _).mp h1
      rw [mem_conjSub]
      convert h2 using 1
      rw [hkdef]; group
    obtain ⟨b₀, hb₀, hnb₀⟩ : ∃ b₀ ∈ B ⊓ Q, b₀ ∉ conjSub l S.V3 := by
      by_contra hcon
      push Not at hcon
      have := Subgroup.relIndex_eq_one.mpr (show B ⊓ Q ≤ conjSub l S.V3 from hcon)
      omega
    have hb₁ : c * b₀ * c⁻¹ ∈ B ⊓ Q :=
      ⟨hcB _ hb₀.1, (Subgroup.mem_normalizer_iff.mp hcQ b₀).mp hb₀.2⟩
    have hnb₁ : c * b₀ * c⁻¹ ∉ conjSub l S.V3 := by
      intro h
      apply hnb₀
      have h' := hcV3 _ h
      have hc2 : c * (c * (c * b₀ * c⁻¹) * c⁻¹) * c⁻¹ = b₀ := by
        have hc' : c * c * c = 1 := by rw [← pow_three']; exact hc3
        calc c * (c * (c * b₀ * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * b₀ * (c * c * c)⁻¹ := by
              group
          _ = b₀ := by rw [hc']; group
      rw [← hc2]
      exact hcV3 _ h'
    exact hnb₀ (hfpf b₀ hb₀.1 (inv_mul_mem_of_relIndex_two hrel hb₀ hb₁ hnb₀ hnb₁))
  have h1 : Nat.card fB.range = 1 := by
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show Nat.card fB.range ∣ 2 ^ 3 from hdvd)
    have hm4 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hm4 with rfl | rfl | rfl | rfl
    · simpa using hm'
    · exact absurd (by simpa using hm') hnot2
    · exact absurd (by rw [hm']; norm_num) hnot4
    · exact absurd (by rw [hm']; norm_num) hnot4
  rw [hcard, Subgroup.relIndex_eq_one] at h1
  exact fun x hx => (h1 hx).2

end NatConj



section Collinear

variable (hNS : ¬ LieModel G .PSp 3 2 1)
  (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz) (h13314 : Stmt13_3_14)
  (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
  {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
  (hDH : F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1)
  (hDγ : F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G))
include hNS h13315 h1356two hG1 h13314 hF s hDH hDγ

theorem exists_collinear_comm (hA1 : F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 S.G1)
    (hb : F8.b T V L S.G1 = 3) :
    ∃ m ∈ L, m * S.z * m⁻¹ ∈ S.V3 ∧ m * S.z * m⁻¹ ≠ S.z ∧
      ∀ u ∈ conjClosure S.V3 S.G1, ∀ w ∈ conjSub m (conjClosure S.V3 S.G1), u * w = w * u := by
  set U := conjClosure S.V3 S.G1 with hUdef
  obtain ⟨k, hk, hAk⟩ := S.exists_A1_le_of_b_eq_three hF s hb
  have hUN : ∀ h ∈ S.G1, ∀ u ∈ U, h * u * h⁻¹ ∈ U := fun h hh u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hh) u).mp hu
  set a := (g : G) * S.z * (g : G)⁻¹ with ha
  have haA : a ∈ F8.A₁ (fsuV1 T V) (g : G) := mul_mem_conjSub ((S.mem_V1_iff).2 (Or.inr rfl))
  set y := k * a * k⁻¹ with hy
  have hyV : y ∈ V := by simpa using mem_conjSub.mp (hAk haA)
  have hyU : y ∈ U := hUN k hk a (hA1 haA)
  have hy3 : y ∈ S.V3 := by
    rw [← S.V_inf_UH hNS h13315 h1356two hG1 h13314]
    exact ⟨hyV, hyU⟩
  have hkz : k * S.z * k⁻¹ = S.z := by
    have h : k * S.z = S.z * k := Subgroup.mem_centralizer_singleton_iff.mp hk
    rw [h, mul_inv_cancel_right]
  have hza : a ≠ S.z ∧ a ≠ 1 := by
    have hz1 := S.z_ne_one
    constructor
    · intro h
      have h1 : a ∈ fsuV1 T V ⊓ F8.A₁ (fsuV1 T V) (g : G) := ⟨(S.mem_V1_iff).2 (Or.inr h), haA⟩
      rw [hF.F913_5b s, Subgroup.mem_bot] at h1
      exact hz1 (h.symm.trans h1)
    · intro h
      apply hz1
      calc S.z = (g : G)⁻¹ * a * (g : G) := by rw [ha]; group
        _ = 1 := by rw [h]; group
  have hyz : y ≠ S.z := by
    intro h
    apply hza.1
    calc a = k⁻¹ * y * k := by rw [hy]; group
      _ = k⁻¹ * (k * S.z * k⁻¹) * k := by rw [h, hkz]
      _ = S.z := by group
  have hy1 : y ≠ 1 := by
    intro h
    apply hza.2
    calc a = k⁻¹ * y * k := by rw [hy]; group
      _ = 1 := by rw [h]; group
  obtain ⟨l, hlL, hly⟩ := S.exists_L_conj_z hyV hy1
  refine ⟨(l : G)⁻¹, L.inv_mem hlL, ?_, ?_, ?_⟩
  · have e : (l : G)⁻¹ * S.z * (l : G)⁻¹⁻¹ = y := by rw [← hly]; group
    rw [e]; exact hy3
  · have e : (l : G)⁻¹ * S.z * (l : G)⁻¹⁻¹ = y := by rw [← hly]; group
    rw [e]; exact hyz
  ·
    have hh' : (l : G) * k * (g : G) ∈ S.G1 := by
      show (l : G) * k * (g : G) ∈ Subgroup.centralizer ({S.z} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e : (l : G) * k * (g : G) * S.z * ((l : G) * k * (g : G))⁻¹ = S.z := by
        calc (l : G) * k * (g : G) * S.z * ((l : G) * k * (g : G))⁻¹ = (l : G) * y * (l : G)⁻¹ := by
              rw [hy, ha]; group
          _ = S.z := hly
      calc (l : G) * k * (g : G) * S.z = (l : G) * k * (g : G) * S.z *
            ((l : G) * k * (g : G))⁻¹ * ((l : G) * k * (g : G)) := by group
        _ = S.z * ((l : G) * k * (g : G)) := by rw [e]
    intro u hu w hw
    have hu' : k⁻¹ * u * k ∈ U := by
      have := hUN _ (S.G1.inv_mem hk) u hu
      simpa using this
    have hw' : k⁻¹ * w * k ∈ F8.Uγ S.V3 S.G1 (g : G) := by
      rw [F8.Uγ, mem_conjSub]
      have hw1 : l * w * (l : G)⁻¹ ∈ U := by
        have := mem_conjSub.mp hw
        simpa using this
      have := hUN _ (S.G1.inv_mem hh') _ hw1
      convert this using 1
      group
    have h := S.comm_UH_Uγ_case1 hF s hDH hDγ hu' hw'
    have h2 : u * w * u⁻¹ * w⁻¹ = 1 := by
      calc u * w * u⁻¹ * w⁻¹ = k * ((k⁻¹ * u * k) * (k⁻¹ * w * k) * (k⁻¹ * u * k)⁻¹ *
            (k⁻¹ * w * k)⁻¹) * k⁻¹ := by group
        _ = 1 := by rw [h]; group
    calc u * w = u * w * u⁻¹ * w⁻¹ * (w * u) := by group
      _ = w * u := by rw [h2, one_mul]

end Collinear


section NatAb

variable (hNS : ¬ LieModel G .PSp 3 2 1)
  (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz) (h13314 : Stmt13_3_14)
  (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) (hhat : ¬ IsHatA6 L)
  {K : Subgroup G} (hKT : K ⊔ T = S.G1)
  {ρ ρ' : ↥S.G1 →* Perm (Fin 6)} {τ : Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
  (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (hker' : ∀ h : ↥S.G1, ρ' h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
  (hKA' : ∀ k : ↥S.G1, (k : G) ∈ K → ρ' k ∈ alternatingGroup (Fin 6))
  (honto' : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ)
  (hE8 : ∀ y : ↥S.G1, (y : G) ∈ pCoreOf 2 (S.L1 ⊔ T) → ρ' y ∈ e8List)
  (hE0 : ∀ y : G, y ∈ pCoreOf 2 (S.L1 ⊔ pCoreOf 2 S.G1) → ∃ hy : y ∈ S.G1, ρ' ⟨y, hy⟩ ∈ e0List)
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (AltHeart 6)} (hβs : Function.Surjective β)
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
      (QuotientAddGroup.mk (permWeight 6 (ρ h) x) : AltHeart 6) = Multiplicative.toAdd (β v))
  {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
  (hDH : F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1)
  (hDγ : F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G))
  (hA1 : F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 S.G1)
include hNS h13315 h1356two hG1 h13314 hF hhat hKT hρ' hN' hker' hKA' honto' hE8 hE0 hβs hβk hβe
  s hDH hDγ hA1

theorem isElemAbelian_UL_nat : IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L) := by
  set U := conjClosure S.V3 S.G1 with hUdef
  by_cases hb : 3 < F8.b T V L S.G1
  · exact S.isElemAbelian_UL_of_lt hF hb
  have hb3 : F8.b T V L S.G1 = 3 := by
    have := hF.three_le_b_and_odd.1
    omega
  obtain ⟨m, hmL, hm3, hmz, hmc⟩ :=
    S.exists_collinear_comm hNS h13315 h1356two hG1 h13314 hF s hDH hDγ hA1 hb3
  have hUN : ∀ h ∈ S.G1, ∀ u ∈ U, h * u * h⁻¹ ∈ U := fun h hh u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hh) u).mp hu
  have hz1 := S.z_ne_one
  have hzV := S.z_mem_V
  refine HypF91.isElemAbelian_conjClosure_of_forall hF.F911_3 fun l hl => ?_
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hlN : l ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hl
  set y := l * S.z * l⁻¹ with hydef
  have hyV : y ∈ V := (Subgroup.mem_normalizer_iff.mp hlN S.z).mp hzV
  by_cases hy3 : y ∈ S.V3
  · by_cases hyz : y = S.z
    ·
      have hlH : l ∈ S.G1 := by
        show l ∈ Subgroup.centralizer ({S.z} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc l * S.z = l * S.z * l⁻¹ * l := by group
          _ = S.z * l := by rw [← hydef, hyz]
      have hw' : w ∈ U := by
        have := hUN l hlH _ (mem_conjSub.mp hw)
        convert this using 1
        group
      exact (isElemAbelian_comm hF.F911_3 hu hw').symm
    ·
      set y₀ := m * S.z * m⁻¹ with hy₀def
      have hmN : m ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hmL
      have hy₀V : y₀ ∈ V := (Subgroup.mem_normalizer_iff.mp hmN S.z).mp hzV
      have hψne : ∀ (v : G) (hv : v ∈ V), v ≠ 1 → ((S.frame.ψ ⟨v, hv⟩ : ↥W4) : P6) ≠ 1 := by
        intro v hv h1 h
        apply h1
        have : (⟨v, hv⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [map_one]; exact Subtype.ext h)
        exact congrArg Subtype.val this
      have hψz : ∀ (v : G) (hv : v ∈ V), v ≠ S.z → ((S.frame.ψ ⟨v, hv⟩ : ↥W4) : P6) ≠ e0123 := by
        intro v hv h1 h
        apply h1
        have : (⟨v, hv⟩ : ↥V) = ⟨S.z, hzV⟩ :=
          S.frame.ψ.injective (by rw [S.psi_z]; exact Subtype.ext h)
        exact congrArg Subtype.val this
      have hy₀1 : y₀ ≠ 1 := by
        intro h
        apply hz1
        calc S.z = m⁻¹ * y₀ * m := by rw [hy₀def]; group
          _ = 1 := by rw [h]; group
      have hy1 : y ≠ 1 := by
        intro h
        apply hz1
        calc S.z = l⁻¹ * y * l := by rw [hydef]; group
          _ = 1 := by rw [h]; group
      obtain ⟨σ, hσ, hσx⟩ := trans_W3 _ _ (S.frame.ψ ⟨y₀, hy₀V⟩).2
        (S.mem_pre.1 hm3).2 (hψne _ _ hy₀1) (hψz _ _ hmz) (S.frame.ψ ⟨y, hyV⟩).2
        (S.mem_pre.1 hy3).2 (hψne _ _ hy1) (hψz _ _ hyz)
      obtain ⟨hs, h4, h5⟩ := a4Fix_facts σ hσ
      obtain ⟨t, htL, hρt⟩ := (S.frame.image_L σ).2 (Perm.mem_alternatingGroup.2 hs)
      have htz : (t : G) * S.z * (t : G)⁻¹ = S.z := by
        rw [S.conj_eq_iff t ⟨S.z, hzV⟩, S.psi_z, hρt]
        exact Subtype.ext (fix_e0123_of σ h4 h5)
      have hty : (t : G) * y₀ * (t : G)⁻¹ = y := by
        have h1 := S.psi_conj t ⟨y₀, hy₀V⟩
        have h2 : S.frame.ψ ⟨(t : G) * y₀ * (t : G)⁻¹, (Subgroup.mem_normalizer_iff.mp t.2 y₀).mp
            hy₀V⟩ = S.frame.ψ ⟨y, hyV⟩ := by
          rw [h1, hρt]
          exact Subtype.ext hσx
        exact congrArg Subtype.val (S.frame.ψ.injective h2)
      have htH : (t : G) ∈ S.G1 := by
        show (t : G) ∈ Subgroup.centralizer ({S.z} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (t : G) * S.z = (t : G) * S.z * (t : G)⁻¹ * t := by group
          _ = S.z * t := by rw [htz]
      have hn : l⁻¹ * t * m ∈ S.G1 := by
        show l⁻¹ * t * m ∈ Subgroup.centralizer ({S.z} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have e : l⁻¹ * t * m * S.z * (l⁻¹ * t * m)⁻¹ = S.z := by
          calc l⁻¹ * t * m * S.z * (l⁻¹ * t * m)⁻¹ = l⁻¹ * ((t : G) * y₀ * (t : G)⁻¹) * l := by
                rw [hy₀def]; group
            _ = S.z := by rw [hty, hydef]; group
        calc l⁻¹ * t * m * S.z = l⁻¹ * t * m * S.z * (l⁻¹ * t * m)⁻¹ * (l⁻¹ * t * m) := by group
          _ = S.z * (l⁻¹ * t * m) := by rw [e]
      have hw1 : l⁻¹ * w * l ∈ U := by simpa using mem_conjSub.mp hw
      have hw' : (t : G)⁻¹ * w * t ∈ conjSub m U := by
        rw [mem_conjSub]
        have := hUN _ (S.G1.inv_mem hn) _ hw1
        convert this using 1
        group
      have hu' : (t : G)⁻¹ * u * t ∈ U := by
        have := hUN _ (S.G1.inv_mem htH) u hu
        simpa using this
      have hc := hmc _ hu' _ hw'
      calc w * u = (t : G) * (((t : G)⁻¹ * w * t) * ((t : G)⁻¹ * u * t)) * (t : G)⁻¹ := by group
        _ = (t : G) * (((t : G)⁻¹ * u * t) * ((t : G)⁻¹ * w * t)) * (t : G)⁻¹ := by rw [hc]
        _ = u * w := by group
  ·
    have hwQ : w ∈ pCoreOf 2 S.G1 :=
      S.conj_UH_le_QH_nat hNS h13315 h1356two hG1 h13314 hF hhat hKT hρ' hN' hker' hKA' honto'
        hE8 hE0 hβs hβk hβe hl hy3 hw
    have hy3' : l⁻¹ * S.z * l⁻¹⁻¹ ∉ S.V3 := by
      intro h
      apply hy3
      have hlN' : l⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hlN
      have h1 := S.mem_pre.1 h
      obtain ⟨hv, h3⟩ := h1
      have e1 := S.psi_conj ⟨l⁻¹, hlN'⟩ ⟨S.z, hzV⟩
      have e2 := S.psi_conj ⟨l, hlN⟩ ⟨S.z, hzV⟩
      refine S.mem_pre.2 ⟨hyV, ?_⟩
      have h3' : InW3 (act4f (S.frame.ρ ⟨l, hlN⟩)⁻¹ e0123) := by
        have := h3
        rw [show (⟨l⁻¹ * S.z * l⁻¹⁻¹, hv⟩ : ↥V) = ⟨(l⁻¹ : G) * S.z * (l⁻¹ : G)⁻¹, _⟩ from rfl,
          e1, S.psi_z] at this
        rw [show (⟨l⁻¹, hlN'⟩ : ↥(Subgroup.normalizer (V : Set G))) = (⟨l, hlN⟩)⁻¹ from rfl,
          map_inv] at this
        exact this
      have := inW3_inv _ h3'
      show InW3 ((S.frame.ψ ⟨l * S.z * l⁻¹, hyV⟩ : ↥W4) : P6)
      rw [show (⟨l * S.z * l⁻¹, hyV⟩ : ↥V) = ⟨(l : G) * S.z * (l : G)⁻¹, _⟩ from rfl, e2,
        S.psi_z]
      exact this
    have huQ : l⁻¹ * u * l ∈ pCoreOf 2 S.G1 := by
      have h := S.conj_UH_le_QH_nat hNS h13315 h1356two hG1 h13314 hF hhat hKT hρ' hN' hker'
        hKA' honto' hE8 hE0 hβs hβk hβe (L.inv_mem hl) hy3'
      apply h
      rw [mem_conjSub, inv_inv]
      convert hu using 1
      group
    have hw1 : l⁻¹ * w * l ∈ U := by simpa using mem_conjSub.mp hw
    have h1 : u * w * u⁻¹ * w⁻¹ ∈ fsuV1 T V := hF.toHypF91.commutator_conjClosure_le u hu w hwQ
    have h2 : l⁻¹ * (w * u * w⁻¹ * u⁻¹) * l ∈ fsuV1 T V := by
      have := hF.toHypF91.commutator_conjClosure_le _ hw1 _ huQ
      convert this using 1
      group
    have h3 : u * w * u⁻¹ * w⁻¹ = 1 := by
      rcases (S.mem_V1_iff).1 h1 with h | h
      · exact h
      · exfalso
        have e : l⁻¹ * (w * u * w⁻¹ * u⁻¹) * l = l⁻¹ * S.z⁻¹ * l := by
          rw [show w * u * w⁻¹ * u⁻¹ = (u * w * u⁻¹ * w⁻¹)⁻¹ by group, h]
        rw [e] at h2
        rcases (S.mem_V1_iff).1 h2 with h' | h'
        · exact hz1 (by
            have : S.z⁻¹ = 1 := by
              calc S.z⁻¹ = l * (l⁻¹ * S.z⁻¹ * l) * l⁻¹ := by group
                _ = 1 := by rw [h']; group
            exact inv_eq_one.mp this)
        · apply hy3
          have hz2 : S.z⁻¹ = S.z := by
            have := isElemAbelian_pow_eq_one hF.toHypF91.elemAbelian hzV
            rw [pow_two] at this
            exact inv_eq_of_mul_eq_one_right this
          have : y = S.z := by
            rw [hydef]
            calc l * S.z * l⁻¹ = l * (l⁻¹ * S.z⁻¹ * l) * l⁻¹ := by rw [h']
              _ = S.z⁻¹ := by group
              _ = S.z := hz2
          rw [this]
          exact S.V1_le_V3 ((S.mem_V1_iff).2 (Or.inr rfl))
    calc w * u = (u * w * u⁻¹ * w⁻¹)⁻¹ * (u * w) := by group
      _ = u * w := by rw [h3, inv_one, one_mul]

end NatAb


section Case1Ab

variable (hNS : ¬ LieModel G .PSp 3 2 1)
  (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz) (h13314 : Stmt13_3_14)
  (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) (hst : S.Struct13827) (hhat : ¬ IsHatA6 L)
  {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
  (hDγ : F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G))
include hNS h13315 h1356two hG1 h13314 hF hst hhat s hDγ

theorem isElemAbelian_UL_case1 :
    IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L) := by
  obtain ⟨K, -, hKT, hL1K, -, hcase, h3⟩ := hst
  rcases hcase with ⟨-, ρ, hker, hKA, honto, hβ⟩ | ⟨hh, -⟩
  swap
  · exact absurd hh hhat
  obtain ⟨hDH, -, -, -, hnQ⟩ := h3 γ γ' g s (Or.inl hDγ)
  have hn : ¬ F8.Uγ V S.G1 (g : G) ≤ ballStab 1 (F8.γ₁ T L S.G1) := fun h =>
    hnQ (h.trans (S.ballStab_γ₁_le_QH hF hKT hL1K ρ hker hKA honto hβ))
  obtain ⟨hA1, y, hyV, hyA⟩ := S.case1_symm hF s hn h3 hDH
  obtain ⟨τ, ρ', hρ', hN', hker', hKA', honto', hE8, hE0⟩ :=
    S.exists_coords hF hKT hL1K ρ hker hKA honto hβ
  rcases hβ with ⟨β, hβs, hβk, hβe⟩ | ⟨β, hβs, hβk, hβe⟩
  · exact S.isElemAbelian_UL_nat hNS h13315 h1356two hG1 h13314 hF hhat hKT hρ' hN' hker' hKA'
      honto' hE8 hE0 hβs hβk hβe s hDH hDγ hA1
  · obtain ⟨R, hR⟩ := S.exists_repRel (Or.inr ⟨β, hβs, hβk, hβe⟩)
    obtain ⟨c, hc, hcV⟩ := exists_conj_Vγ_le hF s
    have hb := S.cover_b_ne_three hNS h13315 h1356two hG1 h13314 hF s hβk hβe hρ' hN' honto' hR
      hker' hE8 hc hcV hyV hyA hA1
    have hb3 := hF.three_le_b_and_odd.1
    exact S.isElemAbelian_UL_of_lt hF (by omega)

end Case1Ab

end Setting4


@[expose] def Input13833Ab : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → S.G1 ∈ S.Hz →
    IsMulCommutative ↥(conjClosure V S.G1) → HypF98 T V L (fsuV1 T V) S.V3 S.G1 →
      S.Struct13827 → ¬ IsHatA6 L →
      ∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
        F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G) →
        IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L) → False

theorem input13833Six_of (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h13314 : Stmt13_3_14) (hAb : Input13833Ab) : Input13833Six := by
  intro G _ _ T L V S hNS hNU hG1 hab hF hst hhat γ γ' g s
  refine lt_of_le_of_ne ?_ fun hDγ => ?_
  · rw [hF.Dγ_eq_inf_pCoreOf s]
    exact inf_le_left
  · exact hAb G T L V S hNS hNU hG1 hab hF hst hhat γ γ' g s hDγ
      (S.isElemAbelian_UL_case1 hNS h13315 h1356two hG1 h13314 hF hst hhat s hDγ)

end CFSG.Quasithin.H13.A6
