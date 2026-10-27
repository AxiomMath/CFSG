module

public import CFSG.Walter.W67.Statements
import CFSG.Walter.W67.Section4.Prop43ab
import CFSG.Walter.W67.Section4.Basic
import CFSG.Walter.W67.W2Cor32A
public import CFSG.Walter.JRFacts

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_le_cyclic [Finite G] {A B : Subgroup G} (hA : IsCyclic A) (hBA : B ≤ A)
    {y : G} (hy : y ∈ Subgroup.normalizer (A : Set G)) : y ∈ Subgroup.normalizer (B : Set G) := by
  set B' := B.map (MulAut.conj y).toMonoidHom
  have hB'A : B' ≤ A := by
    rintro _ ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hy b).mp (hBA hb)
  have hcard : Nat.card (B.subgroupOf A) = Nat.card (B'.subgroupOf A) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'A).toEquiv,
      Subgroup.card_map_of_injective (f := (MulAut.conj y).toMonoidHom) (MulAut.conj y).injective]
  have heq : B.subgroupOf A = B'.subgroupOf A := (IsCyclic.subgroup_eq_iff_card_eq).mpr hcard
  have hBB' : B = B' := by
    have h1 := congrArg (Subgroup.map A.subtype) heq
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hBA, inf_eq_left.mpr hB'A] at h1
  refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
  rw [hBB']
  exact ⟨x, hx, rfl⟩

omit [Finite G] in
theorem sup_aux {V T A E S C : Subgroup G} (h1 : V ⊔ (T ⊔ A ⊔ E) = C) (h2 : V ⊔ T = S) :
    C = A ⊔ (S ⊔ E) := by
  subst h1 h2
  apply le_antisymm
  · exact sup_le (le_sup_of_le_right (le_sup_of_le_left le_sup_left))
      (sup_le (sup_le (le_sup_of_le_right (le_sup_of_le_left le_sup_right)) le_sup_left)
        (le_sup_of_le_right le_sup_right))
  · exact sup_le (le_sup_of_le_right (le_sup_of_le_left le_sup_right))
      (sup_le (sup_le le_sup_left (le_sup_of_le_right (le_sup_of_le_left le_sup_left)))
        (le_sup_of_le_right le_sup_right))

omit [Finite G] in
theorem sup_aux2 {V T A E C : Subgroup G} (h1 : V ⊔ (T ⊔ A ⊔ E) = C) :
    T ≤ C ∧ A ⊔ E ≤ C := by
  subst h1
  exact ⟨le_sup_of_le_right (le_sup_of_le_left le_sup_left),
    sup_le (le_sup_of_le_right (le_sup_of_le_left le_sup_right)) (le_sup_of_le_right le_sup_right)⟩

omit [Finite G] in
theorem sup_aux3 {V T A E C : Subgroup G} (h1 : V ⊔ (T ⊔ A ⊔ E) = C) :
    C = V ⊔ A ⊔ E ⊔ T := by
  subst h1
  apply le_antisymm
  · exact sup_le (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
      (sup_le (sup_le le_sup_right (le_sup_of_le_left (le_sup_of_le_left le_sup_right)))
        (le_sup_of_le_left le_sup_right))
  · exact sup_le (sup_le (sup_le le_sup_left
      (le_sup_of_le_right (le_sup_of_le_left le_sup_right))) (le_sup_of_le_right le_sup_right))
      (le_sup_of_le_right (le_sup_of_le_left le_sup_left))

theorem mem_normalizer_of_normal_sylow {p : ℕ} [Fact p.Prime] {C V : Subgroup G} (hVC : V ≤ C)
    (hV : (V.subgroupOf C).Normal) (hVp : IsPGroup p V)
    (hcard : Nat.card V = p ^ (Nat.card C).factorization p) {y : G}
    (hy : y ∈ Subgroup.normalizer (C : Set G)) : y ∈ Subgroup.normalizer (V : Set G) := by
  set W := V.map (MulAut.conj y).toMonoidHom
  have hWC : W ≤ C := by
    rintro _ ⟨v, hv, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hy v).mp (hVC hv)
  have hWp : IsPGroup p (W.subgroupOf C) :=
    (hVp.map (MulAut.conj y).toMonoidHom).of_equiv (Subgroup.subgroupOfEquivOfLe hWC).symm
  have hVp' : IsPGroup p (V.subgroupOf C) :=
    hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVC).symm
  obtain ⟨Q, hQ⟩ := hWp.exists_le_sylow
  have hVQ : V.subgroupOf C ≤ Q := hVp'.le_sylow_of_normal Q
  have hVQ' : V.subgroupOf C = Q := by
    apply Subgroup.eq_of_le_of_card_ge hVQ
    rw [Sylow.card_eq_multiplicity, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv,
      hcard]
  have hWV : W ≤ V := fun w hw => by
    have h1 : (⟨w, hWC hw⟩ : C) ∈ W.subgroupOf C := hw
    have h2 := hQ h1
    rw [← hVQ'] at h2
    exact h2
  exact JT.mem_normalizer_of_conj_mem fun x hx => hWV ⟨x, hx, rfl⟩

theorem prime_dvd_index_of_mem {C N : Subgroup G} (hCN : C ≤ N) {y : G} (hyN : y ∈ N)
    (hyC : y ∉ C) (hy : y ∈ Subgroup.normalizer (C : Set G)) {r : ℕ} (hr : r.Prime)
    (hyr : y ^ r = 1) : r ∣ (C.subgroupOf N).index := by
  have : Fact r.Prime := ⟨hr⟩
  have hy1 : y ≠ 1 := fun h1 => hyC (h1 ▸ C.one_mem)
  have hyo : orderOf y = r := orderOf_eq_prime hyr hy1
  have hZ : Nat.card (Subgroup.zpowers y) = r := by rw [Nat.card_zpowers, hyo]
  have hZN : Subgroup.zpowers y ≤ Subgroup.normalizer (C : Set G) := Subgroup.zpowers_le.mpr hy
  have hc := card_sup_mul_card_inf_of_le_normalizer hZN
  have hinf : Nat.card (C ⊓ Subgroup.zpowers y : Subgroup G) = 1 := by
    have hdvd : Nat.card (C ⊓ Subgroup.zpowers y : Subgroup G) ∣ r :=
      hZ ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hr).mp hdvd with h | h
    · exact h
    · exfalso
      have heq : C ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hZ])
      have hy' : y ∈ C ⊓ Subgroup.zpowers y := by rw [heq]; exact Subgroup.mem_zpowers y
      exact hyC hy'.1
  rw [hinf, mul_one, hZ] at hc
  have hle : C ⊔ Subgroup.zpowers y ≤ N := sup_le hCN (Subgroup.zpowers_le.mpr hyN)
  have h1 := Subgroup.card_dvd_of_le hle
  have h2 := Subgroup.relIndex_mul_card (H := C) (K := N)
  rw [inf_eq_left.mpr hCN] at h2
  rw [hc, ← h2, mul_comm (Nat.card C)] at h1
  exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos h1

namespace Std

variable (s : Std G)

include s in
theorem hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := index_ne_two_of_perfect s.perfect

theorem exists_E_eq_zpowers :
    ∃ g : G, s.fr.E = Subgroup.zpowers g := by
  obtain ⟨g, -, hg⟩ := s.fr.exists_generator_E
  rw [s.F_eq_bot, sup_bot_eq] at hg
  exact ⟨g, hg.symm⟩

theorem E_comm
    {x y : G} (hx : x ∈ s.fr.E) (hy : y ∈ s.fr.E) : x * y = y * x := by
  obtain ⟨g, hg⟩ := s.exists_E_eq_zpowers
  rw [hg] at hx hy
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_zpow_self g m k).eq

theorem five_lt_q (hp : s.p = 3) : 5 < s.q := by
  have h3 := s.three_lt_q
  have hq : s.q = 3 ^ s.f := by rw [Hyp.q, hp]
  rcases Nat.lt_or_ge s.f 2 with hf | hf
  · interval_cases hf' : s.f
    · exact absurd s.f_pos (by omega)
    · rw [hq, pow_one] at h3
      omega
  · rw [hq]
    calc 5 < 3 ^ 2 := by norm_num
      _ ≤ 3 ^ s.f := Nat.pow_le_pow_right (by norm_num) hf

variable {T₂ : G}

theorem A_le_torus
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) :
    ∃ U₀ : Subgroup G, IsCyclic U₀ ∧ 2 * Nat.card U₀ = s.q + 1 ∧ s.fr.A T₂ ≤ U₀ := by
  have hF := JT.psl2Facts s.K s.iso s.p_ne_two (s.five_lt_q hp)
  obtain ⟨U₀, w, hU, hT₂U, hcard⟩ := hF.even_torus T₂ hT₂.2 h2
  have hC := hU.centralizer_eq hT₂U h2
  have hq4 : s.q % 4 = 3 := by
    have h8 := s.mod_eight
    rw [Hyp.q, hp] at h8 ⊢
    rcases h8 with h8 | h8
    · omega
    · exfalso
      have : (3 : ℕ) ^ s.f % 8 = 1 ∨ (3 : ℕ) ^ s.f % 8 = 3 := by
        rcases Nat.even_or_odd s.f with ⟨k, hk⟩ | ⟨k, hk⟩
        · left; rw [hk, ← two_mul, pow_mul, Nat.pow_mod]; norm_num
        · right; rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
      omega
  have hcard' : 2 * Nat.card U₀ = s.q + 1 := by
    rcases hcard with ⟨-, h⟩ | ⟨h4, -⟩
    · exact h
    · exfalso
      rw [Hyp.q] at hq4
      omega
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (U₀ : Set G) := by
    rw [Subgroup.zpowers_le]
    exact JT.mem_normalizer_of_conj_mem fun x hx => by rw [hU.inv x hx]; exact U₀.inv_mem hx
  refine ⟨U₀, hU.cyclic, hcard', fun x hx => ?_⟩
  have hxC : x ∈ U₀ ⊔ Subgroup.zpowers w := hC ▸ (oddPart_le _ hx)
  obtain ⟨u, hu, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer hwN).mp hxC
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hU.w_mul_self)
    (fun h1 => hU.w_not_mem (h1 ▸ U₀.one_mem))
  rcases eq_one_or_eq_of_mem_zpowers hw2 hy with hy1 | hy1
  · rwa [hy1, mul_one]
  · rw [hy1] at hx
    exfalso
    have hsq : (u * w) * (u * w) = 1 := by
      calc (u * w) * (u * w) = u * (w * u * w⁻¹) * (w * w) := by group
        _ = 1 := by rw [hU.inv u hu, hU.w_mul_self]; group
    have h1 : u * w = 1 := by
      have hodd := odd_orderOf_of_mem_oddPart hx
      have hdvd : orderOf (u * w) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
      have := Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.mpr hodd) (dvd_refl _) hdvd
      exact orderOf_eq_one_iff.mp this
    apply hU.w_not_mem
    rw [eq_inv_of_mul_eq_one_right h1]
    exact U₀.inv_mem hu

theorem isCyclic_A
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) :
    IsCyclic (s.fr.A T₂) := by
  obtain ⟨U₀, hU₀, -, hAU⟩ := s.A_le_torus hp hT₂ h2
  exact Subgroup.isCyclic_of_le hAU

theorem A_inf_E
    (T₂ : G) : s.fr.A T₂ ⊓ s.fr.E = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxA, hxE⟩
  have : x ∈ s.K ⊓ s.fr.E := ⟨(s.fr.A_le T₂ hxA).1, hxE⟩
  rwa [s.fr.K_inf_E] at this

theorem centralizer_V_eq
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) :
    Subgroup.centralizer (s.fr.V T₂ : Set G) = s.fr.A T₂ ⊔ ((s.fr.S : Subgroup G) ⊔ s.fr.E) := by
  obtain ⟨U, -, -, -, -, -, hC, -, hS⟩ := prop_4_3_ab G s.toHyp s.fr hp s.hidx hT₂ h2
  exact sup_aux hC.1 hS.1

theorem comm_of_mem_SE
    {x y : G} (hx : x ∈ (s.fr.S : Subgroup G) ⊔ s.fr.E)
    (hy : y ∈ (s.fr.S : Subgroup G) ⊔ s.fr.E) : x * y = y * x := by
  have hEN : s.fr.E ≤ Subgroup.normalizer ((s.fr.S : Subgroup G) : Set G) :=
    s.fr.E_le_CS.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hEN).mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_sup_iff_of_le_normalizer hEN).mp hy
  have hac := s.fr.comm_of_mem_S ha hc
  have hbd := s.E_comm hb hd
  have hbc : b * c = c * b := (Subgroup.mem_centralizer_iff.mp (s.fr.E_le_CS hb) c hc).symm
  have had : a * d = d * a := Subgroup.mem_centralizer_iff.mp (s.fr.E_le_CS hd) a ha
  calc a * b * (c * d) = a * (b * c) * d := by group
    _ = a * (c * b) * d := by rw [hbc]
    _ = (a * c) * (b * d) := by group
    _ = (c * a) * (d * b) := by rw [hac, hbd]
    _ = c * (a * d) * b := by group
    _ = c * (d * a) * b := by rw [had]
    _ = c * d * (a * b) := by group

theorem SE_le_normalizer_A (hT₂ : T₂ ∈ s.fr.T) :
    (s.fr.S : Subgroup G) ⊔ s.fr.E ≤ Subgroup.normalizer (s.fr.A T₂ : Set G) :=
  sup_le (fun _ hy => JT.mem_normalizer_of_conj_mem fun _ hx => s.fr.S_conj_mem_A hy hx hT₂)
    (fun _ hy => JT.mem_normalizer_of_conj_mem fun _ hx => s.fr.E_conj_mem_A hy hx hT₂)

theorem commutator_centralizer_V
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) :
    ⁅Subgroup.centralizer (s.fr.V T₂ : Set G), Subgroup.centralizer (s.fr.V T₂ : Set G)⁆ =
      s.fr.A T₂ := by
  obtain ⟨U, -, -, -, -, -, hC, hcomm, hS⟩ := prop_4_3_ab G s.toHyp s.fr hp s.hidx hT₂ h2
  have hdec := s.centralizer_V_eq hp hT₂ h2
  apply le_antisymm
  · rw [hdec, Subgroup.commutator_le]
    intro x hx y hy
    have hN := s.SE_le_normalizer_A hT₂
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).mp hx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).mp hy
    have hb : b₁ * b₂ * b₁⁻¹ * b₂⁻¹ = 1 := by
      rw [s.comm_of_mem_SE hb₁ hb₂]; group
    have e : ⁅a₁ * b₁, a₂ * b₂⁆ = a₁ * (b₁ * a₂ * b₁⁻¹) * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) *
        (b₂ * a₁⁻¹ * b₂⁻¹) * a₂⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e, hb, mul_one]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hN hb₁) a₂).mp ha₂
    have h2' := (Subgroup.mem_normalizer_iff.mp (hN hb₂) a₁⁻¹).mp (Subgroup.inv_mem _ ha₁)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha₁ h1) h2')
      (Subgroup.inv_mem _ ha₂)
  · rw [← hcomm]
    obtain ⟨h1, h2⟩ := sup_aux2 hC.1
    exact Subgroup.commutator_mono h1 h2

theorem normalizer_V_le
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    {Aα : Subgroup G} (hAα : Aα ≤ s.fr.A T₂) :
    Subgroup.normalizer (s.fr.V T₂ : Set G) ≤ Subgroup.normalizer (Aα : Set G) := by
  intro y hy
  have hyC := normalizer_le_normalizer_centralizer _ hy
  have hyA : y ∈ Subgroup.normalizer (s.fr.A T₂ : Set G) := by
    rw [← s.commutator_centralizer_V hp hT₂ h2]
    exact JT.mem_normalizer_of_conj_mem fun x hx => conj_mem_commutator_of_mem_normalizer hyC hx
  exact mem_normalizer_of_le_cyclic (s.isCyclic_A hp hT₂ h2) hAα hyA

theorem not_le_centralizer
    (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) {Aα : Subgroup G}
    (hAα : Aα ≤ s.fr.A T₂) (hne : Aα ≠ ⊥) {τ : G} (hτS : τ ∈ (s.fr.S : Subgroup G))
    (hτV : τ ∉ s.fr.V T₂) : τ ∉ Subgroup.centralizer (Aα : Set G) := by
  intro hτ
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have h1 := s.fr.S_inv_A hT₂ h2 hτS hτV (hAα ha)
  have h3 : τ * a * τ⁻¹ = a := by
    rw [(Subgroup.mem_centralizer_iff.mp hτ a ha).symm, mul_inv_cancel_right]
  rw [h3] at h1
  have hodd := odd_orderOf_of_mem_oddPart (hAα ha)
  have : a * a = 1 := by
    calc a * a = a⁻¹⁻¹ * a := by rw [inv_inv]
      _ = 1 := by rw [← h1, inv_mul_cancel]
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact this)
  exact ha1' (orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.mpr hodd) (dvd_refl _) hdvd))

theorem A_le_centralizer_V (T₂ : G) : s.fr.A T₂ ≤ Subgroup.centralizer (s.fr.V T₂ : Set G) :=
  fun x hx => by
    rw [s.fr.centralizer_V]
    exact ⟨s.K_le_H (s.fr.A_le T₂ hx).1, (s.fr.A_le T₂ hx).2⟩

theorem factorization_centralizer
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    {Aα : Subgroup G} (hAα : Aα ≤ s.fr.A T₂) (hne : Aα ≠ ⊥) :
    (Nat.card (Subgroup.centralizer (Aα : Set G))).factorization 2 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (Aα : Set G)
  have hVC : s.fr.V T₂ ≤ C :=
    Subgroup.le_centralizer_iff.mpr (hAα.trans (s.A_le_centralizer_V T₂))
  have hVS := s.fr.V_le_S hT₂
  have hV2 : IsPGroup 2 ((s.fr.V T₂).subgroupOf C) :=
    (s.fr.S.isPGroup'.to_le hVS).of_equiv (Subgroup.subgroupOfEquivOfLe hVC).symm
  obtain ⟨P, hP⟩ := hV2.exists_le_sylow
  set P' := (P : Subgroup C).map C.subtype
  have hP'C : P' ≤ C := Subgroup.map_subtype_le _
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map _
  have hVP' : s.fr.V T₂ ≤ P' := fun v hv => ⟨⟨v, hVC hv⟩, hP hv, rfl⟩
  have hP'card : Nat.card P' = 4 := by
    apply le_antisymm
    · by_contra hgt
      push Not at hgt
      have h8 := s.card_le_eight hP'2
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP'2
      have hk3 : k = 3 := by
        have h1 : 4 < 2 ^ k := hk ▸ hgt
        have h2' : 2 ^ k ≤ 8 := hk ▸ h8
        have hk' : k ≤ 3 := by
          by_contra h
          push Not at h
          have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h
          omega
        interval_cases k <;> omega
      subst hk3
      have hP'syl : Nat.card P' = 2 ^ (Nat.card G).factorization 2 := by
        rw [hk, ← Sylow.card_eq_multiplicity s.fr.S, s.fr.card_S]
        norm_num
      have hab := s.isMulCommutative_of_isPGroup hP'2
      have hP'CV : P' ≤ Subgroup.centralizer (s.fr.V T₂ : Set G) := fun y hy =>
        Subgroup.mem_centralizer_iff.mpr fun v hv =>
          congrArg Subtype.val (hab.is_comm.comm ⟨v, hVP' hv⟩ ⟨y, hy⟩)
      have hSCV : (s.fr.S : Subgroup G) ≤ Subgroup.centralizer (s.fr.V T₂ : Set G) := fun y hy =>
        Subgroup.mem_centralizer_iff.mpr fun v hv => s.fr.comm_of_mem_S (hVS hv) hy
      obtain ⟨l, hl, hlP⟩ := exists_conj_le_of_sylow s.fr.S (Sylow.ofCard P' hP'syl) hSCV
        (by rw [Sylow.coe_ofCard]; exact hP'CV)
      rw [Sylow.coe_ofCard] at hlP
      have hlN := s.normalizer_V_le hp hT₂ h2 hAα (Subgroup.centralizer_le_normalizer _ hl)
      have hmap : P'.map (MulAut.conj l).toMonoidHom = (s.fr.S : Subgroup G) := by
        refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
        · obtain ⟨y, hy, rfl⟩ := hx
          exact hlP y hy
        · rw [Subgroup.card_map_of_injective (f := (MulAut.conj l).toMonoidHom)
            (MulAut.conj l).injective, hk, s.fr.card_S]
          norm_num
      obtain ⟨τ, hτS, hτV⟩ : ∃ τ ∈ (s.fr.S : Subgroup G), τ ∉ s.fr.V T₂ := by
        by_contra hcon
        push Not at hcon
        have := Subgroup.card_le_of_le (fun x hx => hcon x hx : (s.fr.S : Subgroup G) ≤ s.fr.V T₂)
        rw [s.fr.card_S, s.fr.card_V hT₂ h2] at this
        omega
      apply s.not_le_centralizer hT₂ h2 hAα hne hτS hτV
      rw [← hmap] at hτS
      obtain ⟨y, hy, rfl⟩ := hτS
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have ha' : l⁻¹ * a * l⁻¹⁻¹ ∈ Aα :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlN) a).mp ha
      have hya := Subgroup.mem_centralizer_iff.mp (hP'C hy) _ ha'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc a * (l * y * l⁻¹) = l * ((l⁻¹ * a * l⁻¹⁻¹) * y) * l⁻¹ := by group
        _ = l * (y * (l⁻¹ * a * l⁻¹⁻¹)) * l⁻¹ := by rw [hya]
        _ = l * y * l⁻¹ * a := by group
    · rw [← s.fr.card_V hT₂ h2]
      exact Subgroup.card_le_of_le hVP'
  have hPcard : Nat.card (P : Subgroup C) = 4 := by
    rw [← hP'card, Subgroup.card_map_of_injective C.subtype_injective]
  have := Sylow.card_eq_multiplicity P
  rw [hPcard, show (4 : ℕ) = 2 ^ 2 by norm_num] at this
  exact (Nat.pow_right_injective (le_refl 2) this).symm

theorem A_le_centralizer_of_le
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    {Aα : Subgroup G} (hAα : Aα ≤ s.fr.A T₂) :
    s.fr.A T₂ ≤ Subgroup.centralizer (Aα : Set G) := by
  have hcyc := s.isCyclic_A hp hT₂ h2
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact congrArg Subtype.val
    ((IsCyclic.isMulCommutative (α := s.fr.A T₂)).is_comm.comm ⟨a, hAα ha⟩ ⟨x, hx⟩)

theorem normalizer_eq_of
    (h42 : S_lemma_4_2) (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T)
    (h2 : orderOf T₂ = 2) {Aα : Subgroup G} (hAα : Aα ≤ s.fr.A T₂) (hne : Aα ≠ ⊥) :
    Subgroup.normalizer (Aα : Set G) = Subgroup.normalizer (s.fr.V T₂ : Set G) := by
  refine le_antisymm (fun y hy => ?_) (s.normalizer_V_le hp hT₂ h2 hAα)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAC := s.A_le_centralizer_of_le hp hT₂ h2 hAα
  have hVC : s.fr.V T₂ ≤ Subgroup.centralizer (Aα : Set G) :=
    Subgroup.le_centralizer_iff.mpr (hAα.trans (s.A_le_centralizer_V T₂))
  have hfac := s.factorization_centralizer hp hT₂ h2 hAα hne
  have hn := h42 G s hp hT₂ h2 _ (sup_le hAC hVC) hfac
  refine mem_normalizer_of_normal_sylow hVC hn (s.fr.S.isPGroup'.to_le (s.fr.V_le_S hT₂)) ?_
    (normalizer_le_normalizer_centralizer _ hy)
  rw [hfac, s.fr.card_V hT₂ h2]
  norm_num

theorem V_A_E_le_centralizer
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    {Aα : Subgroup G} (hAα : Aα ≤ s.fr.A₀ T₂) :
    s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E ≤ Subgroup.centralizer (Aα : Set G) := by
  have hAα' : Aα ≤ s.fr.A T₂ := hAα.trans inf_le_left
  refine sup_le (sup_le ?_ (s.A_le_centralizer_of_le hp hT₂ h2 hAα')) ?_
  · exact Subgroup.le_centralizer_iff.mpr (hAα'.trans (s.A_le_centralizer_V T₂))
  · exact Subgroup.le_centralizer_iff.mpr (hAα.trans inf_le_right)

theorem exists_mem_S_not_mem_V (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) :
    ∃ τ ∈ (s.fr.S : Subgroup G), τ ∉ s.fr.V T₂ := by
  by_contra hcon
  push Not at hcon
  have := Subgroup.card_le_of_le (fun x hx => hcon x hx : (s.fr.S : Subgroup G) ≤ s.fr.V T₂)
  rw [s.fr.card_S, s.fr.card_V hT₂ h2] at this
  omega

theorem card_normalizer_V
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    {Aα : Subgroup G} (hAα : Aα ≤ s.fr.A₀ T₂) (hne : Aα ≠ ⊥) :
    Nat.card (Subgroup.normalizer (s.fr.V T₂ : Set G)) =
      6 * Nat.card (s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E : Subgroup G) := by
  have hAα' : Aα ≤ s.fr.A T₂ := hAα.trans inf_le_left
  obtain ⟨U, hU3, hNV, -, hUV, hT₁2, hC, -, hS⟩ := prop_4_3_ab G s.toHyp s.fr hp s.hidx hT₂ h2
  generalize hT₁ : (s.fr.S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) = T₁ at hT₁2 hC hS
  have hT₁S : T₁ ≤ (s.fr.S : Subgroup G) := hT₁ ▸ inf_le_left
  have hXC := s.V_A_E_le_centralizer hp hT₂ h2 hAα
  generalize hX : s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E = X at hXC ⊢
  have hCV : Subgroup.centralizer (s.fr.V T₂ : Set G) = X ⊔ T₁ := hX ▸ sup_aux3 hC.1
  have hSN : (s.fr.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := fun y hy => by
    rw [← hX]
    refine mem_normalizer_sup (mem_normalizer_sup ?_ ?_) ?_
    · refine JT.mem_normalizer_of_conj_mem fun v hv => ?_
      rw [s.fr.comm_of_mem_S hy (s.fr.V_le_S hT₂ hv), mul_inv_cancel_right]
      exact hv
    · exact JT.mem_normalizer_of_conj_mem fun x hx => s.fr.S_conj_mem_A hy hx hT₂
    · refine JT.mem_normalizer_of_conj_mem fun e he => ?_
      rw [Subgroup.mem_centralizer_iff.mp (s.fr.E_le_CS he) y hy, mul_inv_cancel_right]
      exact he
  have hXT : X ⊓ T₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxX, hxT⟩
    by_contra hx1
    have hxV : x ∈ s.fr.V T₂ := by
      by_contra hxV
      exact s.not_le_centralizer hT₂ h2 hAα' hne (hT₁S hxT) hxV (hXC hxX)
    have : x ∈ s.fr.V T₂ ⊓ T₁ := ⟨hxV, hxT⟩
    rw [disjoint_iff.mp hS.2.1] at this
    exact hx1 this
  have hc1 := card_sup_mul_card_inf_of_le_normalizer (hT₁S.trans hSN)
  rw [hXT, Subgroup.card_bot, mul_one, hT₁2, ← hCV] at hc1
  have hUNV : U ≤ Subgroup.normalizer (s.fr.V T₂ : Set G) := by rw [hNV]; exact le_sup_left
  have hUN := hUNV.trans (normalizer_le_normalizer_centralizer _)
  have hc2 := card_sup_mul_card_inf_of_le_normalizer hUN
  have hinf : Nat.card (Subgroup.centralizer (s.fr.V T₂ : Set G) ⊓ U : Subgroup G) = 1 := by
    have hdvd : Nat.card (Subgroup.centralizer (s.fr.V T₂ : Set G) ⊓ U : Subgroup G) ∣ 3 :=
      hU3 ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exfalso
      have heq : Subgroup.centralizer (s.fr.V T₂ : Set G) ⊓ U = U :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hU3])
      have hUC : U ≤ Subgroup.centralizer (s.fr.V T₂ : Set G) := by
        rw [← heq]
        exact inf_le_left
      have hbot : ⁅U, s.fr.V T₂⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hUC
      rw [hUV] at hbot
      have hc := s.fr.card_V hT₂ h2
      rw [hbot, Subgroup.card_bot] at hc
      omega
  rw [hinf, mul_one, hU3, sup_comm, ← hNV, hc1] at hc2
  rw [hc2]
  ring

theorem centralizer_eq_and_index
    (h42 : S_lemma_4_2) (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T)
    (h2 : orderOf T₂ = 2) {Aα : Subgroup G} (hAα : Aα ≤ s.fr.A₀ T₂) (hne : Aα ≠ ⊥)
    (h3 : ∃ y ∈ Subgroup.normalizer (Aα : Set G), y ∉ Subgroup.centralizer (Aα : Set G) ∧
      y ^ 3 = 1) :
    Subgroup.centralizer (Aα : Set G) = s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E ∧
      ((Subgroup.centralizer (Aα : Set G)).subgroupOf
        (Subgroup.normalizer (Aα : Set G))).index = 6 := by
  have hAα' : Aα ≤ s.fr.A T₂ := hAα.trans inf_le_left
  have hN := s.normalizer_eq_of h42 hp hT₂ h2 hAα' hne
  have hcard := s.card_normalizer_V hp hT₂ h2 hAα hne
  have hXC := s.V_A_E_le_centralizer hp hT₂ h2 hAα
  have hCN : Subgroup.centralizer (Aα : Set G) ≤ Subgroup.normalizer (Aα : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hCnorm : Subgroup.normalizer (Aα : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (Aα : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer _
  obtain ⟨τ, hτS, hτV⟩ := s.exists_mem_S_not_mem_V hT₂ h2
  have hτN : τ ∈ Subgroup.normalizer (Aα : Set G) := by
    rw [hN]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
      s.fr.comm_of_mem_S (s.fr.V_le_S hT₂ hv) hτS)
  have h2i := prime_dvd_index_of_mem hCN hτN (s.not_le_centralizer hT₂ h2 hAα' hne hτS hτV)
    (hCnorm hτN) Nat.prime_two (by rw [pow_two]; exact s.fr.mul_self_of_mem_S hτS)
  obtain ⟨y, hyN, hyC, hy3⟩ := h3
  have h3i := prime_dvd_index_of_mem hCN hyN hyC (hCnorm hyN) Nat.prime_three hy3
  have h6 : 6 ∣ ((Subgroup.centralizer (Aα : Set G)).subgroupOf
      (Subgroup.normalizer (Aα : Set G))).index :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2i h3i
  have hi := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (Aα : Set G))
    (K := Subgroup.normalizer (Aα : Set G))
  rw [inf_eq_left.mpr hCN] at hi
  have hNcard : Nat.card (Subgroup.normalizer (Aα : Set G)) =
      6 * Nat.card (s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E : Subgroup G) := by rw [hN]; exact hcard
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hXC
  obtain ⟨j, hj⟩ := h6
  change ((Subgroup.centralizer (Aα : Set G)).subgroupOf _).index * _ = _ at hi
  rw [hNcard, hk, hj] at hi
  have hXpos : 0 < Nat.card (s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E : Subgroup G) := Nat.card_pos
  have hjk : j * k = 1 := by
    have : 6 * (j * k) * Nat.card (s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E : Subgroup G) =
        6 * 1 * Nat.card (s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E : Subgroup G) := by
      rw [← hi]; ring
    have := Nat.eq_of_mul_eq_mul_right hXpos this
    omega
  have hk1 : k = 1 := Nat.dvd_one.mp (Dvd.intro_left j hjk)
  have hj1 : j = 1 := Nat.dvd_one.mp (Dvd.intro k hjk)
  refine ⟨(Subgroup.eq_of_le_of_card_ge hXC (by rw [hk, hk1, mul_one])).symm, ?_⟩
  rw [hj, hj1]

end Std

end CFSG.Walter.W67
