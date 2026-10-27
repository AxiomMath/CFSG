module

public import CFSG.RankThree.PartOne.S12.TerminalWeylPerm
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.Quasithin.Background.C2PushLift
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.S152He9A5
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.He10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
open scoped commutatorElement Pointwise

theorem perm_five_no_fixed :
    ∀ c : Equiv.Perm (Fin 5), c ^ 5 = 1 → c ≠ 1 → ∀ p, c p ≠ p := by decide +kernel

theorem perm_fixed_pt_unique :
    ∀ v : Equiv.Perm (Fin 5), v ^ 2 = 1 → v ≠ 1 → Equiv.Perm.sign v = 1 →
      ∃ p, v p = p ∧ ∀ q, v q = q → q = p := by decide +kernel

theorem perm_even_four_two :
    ∀ v : Equiv.Perm (Fin 5), Equiv.Perm.sign v = 1 → v ^ 4 = 1 → v ^ 2 = 1 := by decide +kernel

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have : Nontrivial (Fin 5) := Fin.nontrivial_iff_two_le.2 (by norm_num)
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_dvd_four_of_two_subgroup {V : Subgroup (Equiv.Perm (Fin 5))}
    (hVA : V ≤ alternatingGroup (Fin 5)) (hV2 : IsPGroup 2 V) : Nat.card V ∣ 4 := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hV2
  have hdvd : Nat.card V ∣ 60 := card_alternatingGroup_five ▸ Subgroup.card_dvd_of_le hVA
  rw [ha] at hdvd ⊢
  have : 2 ^ a ∣ 4 * 15 := by simpa using hdvd
  have hcop : Nat.Coprime (2 ^ a) 15 := Nat.Coprime.pow_left _ (by norm_num)
  exact hcop.dvd_of_dvd_mul_right this

theorem perm_five_eq_one_of_normalizes (c : Equiv.Perm (Fin 5)) (hc : c ^ 5 = 1)
    (V : Subgroup (Equiv.Perm (Fin 5))) (hVA : V ≤ alternatingGroup (Fin 5)) (hV2 : IsPGroup 2 V)
    (hVne : V ≠ ⊥) (hcV : ∀ v ∈ V, c * v * c⁻¹ ∈ V) : c = 1 := by
  by_contra hc1
  have hdvd4 : Nat.card V ∣ 4 := card_dvd_four_of_two_subgroup hVA hV2
  have hcard4 : Nat.card V ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd4
  obtain ⟨⟨v, hvV⟩, hv1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  have hv1 : v ≠ 1 := fun h => hv1' (Subtype.ext h)
  have hv4 : (v : Equiv.Perm (Fin 5)) ^ 4 = 1 := by
    have h1 : (⟨v, hvV⟩ : ↥V) ^ Nat.card ↥V = 1 := pow_card_eq_one'
    obtain ⟨t, ht⟩ := hdvd4
    have h2 : (⟨v, hvV⟩ : ↥V) ^ 4 = 1 := by rw [ht, pow_mul, h1, one_pow]
    simpa using congrArg Subtype.val h2
  have hvsign : Equiv.Perm.sign v = 1 := (Equiv.Perm.mem_alternatingGroup.mp (hVA hvV))
  have hv2 : v ^ 2 = 1 := perm_even_four_two v hvsign hv4
  obtain ⟨p, hp, hpu⟩ := perm_fixed_pt_unique v hv2 hv1 hvsign
  have hconj : ∀ n : ℕ, c ^ n * v * (c ^ n)⁻¹ ∈ V := by
    intro n
    induction n with
    | zero => simpa using hvV
    | succ n ih =>
      have := hcV _ ih
      have e : c * (c ^ n * v * (c ^ n)⁻¹) * c⁻¹ = c ^ (n + 1) * v * (c ^ (n + 1))⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rwa [e] at this
  have key : ∀ a b : ℕ, a < b → b < 5 → c ^ a * v * (c ^ a)⁻¹ ≠ c ^ b * v * (c ^ b)⁻¹ := by
    intro a b hab hb5 heq
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
    set w : Equiv.Perm (Fin 5) := c ^ (k + 1) with hw
    have hcomm : w * v = v * w := by
      have h1 : c ^ a * v * (c ^ a)⁻¹ = c ^ a * (w * v * w⁻¹) * (c ^ a)⁻¹ := by
        rw [heq]
        have : c ^ (a + k + 1) = c ^ a * w := by rw [hw, ← pow_add]; congr 1
        rw [this, mul_inv_rev]
        group
      have h2 : v = w * v * w⁻¹ :=
        calc v = (c ^ a)⁻¹ * (c ^ a * v * (c ^ a)⁻¹) * c ^ a := by group
          _ = (c ^ a)⁻¹ * (c ^ a * (w * v * w⁻¹) * (c ^ a)⁻¹) * c ^ a := by rw [h1]
          _ = w * v * w⁻¹ := by group
      calc w * v = (w * v * w⁻¹) * w := by group
        _ = v * w := by rw [← h2]
    have hw5 : w ^ 5 = 1 := by rw [hw, ← pow_mul, mul_comm, pow_mul, hc, one_pow]
    have hw1 : w ≠ 1 := by
      intro hw1
      have hgcd : Nat.gcd (k + 1) 5 = 1 := by
        have hk : k < 4 := by omega
        interval_cases k <;> decide
      have h1 : c ^ Nat.gcd (k + 1) 5 = 1 := pow_gcd_eq_one.mpr ⟨hw1, hc⟩
      rw [hgcd, pow_one] at h1
      exact hc1 h1
    have hwp : w p = p := by
      have h1 : v (w p) = w p := by
        have := congrArg (fun f : Equiv.Perm (Fin 5) => f p) hcomm
        simp only [Equiv.Perm.mul_apply] at this
        rw [← this, hp]
      exact hpu _ h1
    exact perm_five_no_fixed w hw5 hw1 p hwp
  classical
  have : Fintype ↥V := Fintype.ofFinite _
  let f : Fin 5 → ↥V := fun i => ⟨c ^ (i : ℕ) * v * (c ^ (i : ℕ))⁻¹, hconj i⟩
  have hlt : Fintype.card ↥V < Fintype.card (Fin 5) := by
    rw [← Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  have hfeq : c ^ (i : ℕ) * v * (c ^ (i : ℕ))⁻¹ = c ^ (j : ℕ) * v * (c ^ (j : ℕ))⁻¹ :=
    congrArg Subtype.val hfij
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = j => hij (Fin.ext h)) with h | h
  · exact key i j h j.2 hfeq
  · exact key j i h i.2 hfeq.symm

theorem rho_eq_one {A : Type*} [Group A] (ρ : A →* Equiv.Perm (Fin 5)) (Kh : Subgroup A)
    (e : ↥Kh ≃* ↥(alternatingGroup (Fin 5)))
    (hρK : ∀ (y : A) (hy : y ∈ Kh), ρ y = ((e ⟨y, hy⟩ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)))
    (P : Subgroup A) (hPK : P ≤ Kh) (hP2 : IsPGroup 2 P) (hPne : P ≠ ⊥)
    (yh : A) (hy5 : yh ^ 5 = 1) (hyP : ∀ x ∈ P, yh * x * yh⁻¹ ∈ P) : ρ yh = 1 := by
  refine perm_five_eq_one_of_normalizes (ρ yh) (by rw [← map_pow, hy5, map_one]) (P.map ρ) ?_
    (hP2.map ρ) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [hρK x (hPK hx)]
    exact (e ⟨x, hPK hx⟩).2
  · obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hPne
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hρx : ρ x ≠ 1 := by
      rw [hρK x (hPK hx)]
      intro h
      have h1 : (e ⟨x, hPK hx⟩ : ↥(alternatingGroup (Fin 5))) = 1 := Subtype.ext h
      have h2 := (map_eq_one_iff e e.injective).1 h1
      exact hx1' (congrArg Subtype.val h2)
    exact (Subgroup.ne_bot_iff_exists_ne_one).mpr
      ⟨⟨ρ x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩⟩, fun h => hρx (congrArg Subtype.val h)⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_map.mpr ⟨_, hyP x hx, by rw [map_mul, map_mul, map_inv]⟩

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_rho {G₀ K : Subgroup G} (hKG : K ≤ G₀) (hKn : (K.subgroupOf G₀).Normal)
    (hA5 : Nonempty (OTwoQuot K ≃* ↥(alternatingGroup (Fin 5)))) :
    ∃ (ρ : OTwoQuot G₀ →* Equiv.Perm (Fin 5)) (e : ↥(imageOTwoQuot G₀ K) ≃* ↥(alternatingGroup (Fin 5))),
      (∀ (y : OTwoQuot G₀) (hy : y ∈ imageOTwoQuot G₀ K),
        ρ y = ((e ⟨y, hy⟩ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))) ∧
      ∀ g : OTwoQuot G₀, ρ g = 1 → ∀ y ∈ imageOTwoQuot G₀ K, g * y = y * g := by
  have hKsub : IsSubnormal K G₀ := A4.subnormal_of_normal hKG hKn
  obtain ⟨e1⟩ := C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot hKsub
  obtain ⟨eA⟩ := hA5
  let eOpen : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* OTwoQuot K :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)
  let e : ↥(imageOTwoQuot G₀ K) ≃* ↥(alternatingGroup (Fin 5)) := e1.symm.trans (eOpen.trans eA)
  have hKhn : (imageOTwoQuot G₀ K).Normal := hKn.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨π, hπ1, hπ2⟩ := CFSG.RankThree.PartOne.TerminalPerm.exists_pi_of_equiv
    (Γ := ⊤) (Y := imageOTwoQuot G₀ K) e le_top (fun g _ y hy => hKhn.conj_mem y hy g)
  refine ⟨π.comp (Subgroup.topEquiv (G := OTwoQuot G₀)).symm.toMonoidHom, e, fun y hy => hπ1 y hy, ?_⟩
  intro g hg y hy
  exact hπ2 ⟨g, Subgroup.mem_top g⟩ hg y hy

theorem not_le_pCoreOf_of_sylow {G₀ K R : Subgroup G} (hKG : K ≤ G₀)
    (hA5 : Nonempty (OTwoQuot K ≃* ↥(alternatingGroup (Fin 5)))) (hRK : IsSylowTwoOf (R ⊓ K) K) :
    ¬ (R ⊓ K ≤ pCoreOf 2 G₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hle
  obtain ⟨eA⟩ := hA5
  have hOK : pCoreOf 2 K ≤ R ⊓ K :=
    A4.le_of_normal_of_isSylowTwoOf hRK (pCoreOf_le 2 K)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 K)).2
        (le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hKO : pCoreOf 2 G₀ ⊓ K ≤ pCoreOf 2 K := by
    refine le_pCoreOf_of_le_normalizer inf_le_right ?_ ((pCoreOf_isPGroup 2 G₀).to_le inf_le_left)
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pCoreOf 2 G₀ (hKG hx), Subgroup.le_normalizer hx⟩
  have heq : R ⊓ K = pCoreOf 2 K := le_antisymm (fun x hx => hKO ⟨hle hx, hx.2⟩) hOK
  have hsub : (pCoreOf 2 K).subgroupOf K = CFSG.Open.pCore 2 ↥K :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have h60 : Nat.card (OTwoQuot K) = 60 := by
    rw [Nat.card_congr eA.toEquiv, card_alternatingGroup_five]
  have hodd := hRK.2.2
  rw [heq, hsub] at hodd
  apply hodd
  have : ((CFSG.Open.pCore 2 ↥K).index) = Nat.card (OTwoQuot K) := rfl
  rw [this, h60]
  norm_num

theorem commutator_le_of_five {G₀ K R Y : Subgroup G}
    (hKG : K ≤ G₀) (hKn : (K.subgroupOf G₀).Normal)
    (hA5 : Nonempty (OTwoQuot K ≃* ↥(alternatingGroup (Fin 5))))
    (hR2 : IsPGroup 2 R) (hYG : Y ≤ G₀)
    (hYR : Y ≤ Subgroup.normalizer (R : Set G)) (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hRK : IsSylowTwoOf (R ⊓ K) K) (hY : Y = oTwoUpper Y)
    (hY5 : ∀ y ∈ Y, Odd (orderOf y) → y ^ 5 = 1) :
    ⁅Y, K⁆ ≤ pCoreOf 2 G₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρ, e, hρK, hρker⟩ := exists_rho hKG hKn hA5
  have hPne := not_le_pCoreOf_of_sylow hKG hA5 hRK
  have hRKG : R ⊓ K ≤ G₀ := inf_le_right.trans hKG
  have hP2 : IsPGroup 2 (imageOTwoQuot G₀ (R ⊓ K)) := by
    unfold imageOTwoQuot
    exact (A4.isPGroup_subgroupOf_of_le hRKG hR2.to_inf_left).map _
  have hP1 : imageOTwoQuot G₀ (R ⊓ K) ≠ ⊥ := by
    obtain ⟨r, hr, hr0⟩ := Set.not_subset.1 hPne
    intro hbot
    have hmem : (QuotientGroup.mk ⟨r, hRKG hr⟩ : OTwoQuot G₀) ∈ imageOTwoQuot G₀ (R ⊓ K) :=
      mem_imageOTwoQuot_iff.mpr ⟨r, hRKG hr, hr, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hr0 ((mk_eq_one_iff_mem_pCoreOf ⟨r, hRKG hr⟩).1 hmem)
  have hPK : imageOTwoQuot G₀ (R ⊓ K) ≤ imageOTwoQuot G₀ K := imageOTwoQuot_mono inf_le_right
  have hy1 : ∀ y (hy : y ∈ Y), y ^ 5 = 1 →
      ρ (QuotientGroup.mk ⟨y, hYG hy⟩) = 1 := by
    intro y hy hy5
    refine rho_eq_one ρ (imageOTwoQuot G₀ K) e hρK (imageOTwoQuot G₀ (R ⊓ K)) hPK hP2 hP1 _ ?_ ?_
    · rw [← QuotientGroup.mk_pow]
      have : (⟨y, hYG hy⟩ : ↥G₀) ^ 5 = 1 := Subtype.ext (by simpa using hy5)
      rw [this]
      rfl
    · intro x hx
      obtain ⟨r, hrG, hr, rfl⟩ := mem_imageOTwoQuot_iff.mp hx
      have hr' : y * r * y⁻¹ ∈ R ⊓ K :=
        ⟨(Subgroup.mem_normalizer_iff.mp (hYR hy) r).mp hr.1,
          (Subgroup.mem_normalizer_iff.mp (hYK hy) r).mp hr.2⟩
      have hrG' : y * r * y⁻¹ ∈ G₀ := G₀.mul_mem (G₀.mul_mem (hYG hy) hrG) (G₀.inv_mem (hYG hy))
      have hmem : (QuotientGroup.mk ⟨y * r * y⁻¹, hrG'⟩ : OTwoQuot G₀) ∈
          imageOTwoQuot G₀ (R ⊓ K) := mem_imageOTwoQuot_iff.mpr ⟨_, hrG', hr', rfl⟩
      have : (QuotientGroup.mk ⟨y * r * y⁻¹, hrG'⟩ : OTwoQuot G₀) =
          QuotientGroup.mk ⟨y, hYG hy⟩ * QuotientGroup.mk ⟨r, hrG⟩ *
            (QuotientGroup.mk ⟨y, hYG hy⟩)⁻¹ := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        rfl
      rw [← this]
      exact hmem
  set C : Subgroup G := ((Subgroup.centralizer (imageOTwoQuot G₀ K : Set (OTwoQuot G₀))).comap
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥G₀))).map G₀.subtype with hC
  have hYC : Y ≤ C := by
    rw [hY]
    refine (Subgroup.closure_le C).mpr fun x hx => ?_
    have hx5 : x ^ 5 = 1 := hY5 x hx.1 hx.2
    refine Subgroup.mem_map.mpr ⟨⟨x, hYG hx.1⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hρker _ (hy1 x hx.1 hx5) k hk).symm
  rw [Subgroup.commutator_le]
  intro y hy k hk
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp (hYC hy)
  have hgc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hg)
    (QuotientGroup.mk ⟨k, hKG hk⟩) (mem_imageOTwoQuot_iff.mpr ⟨k, hKG hk, hk, rfl⟩)
  have h1 : (QuotientGroup.mk (g * ⟨k, hKG hk⟩ * g⁻¹ * ⟨k, hKG hk⟩⁻¹) : OTwoQuot G₀) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    have hgc' : (QuotientGroup.mk g : OTwoQuot G₀) * QuotientGroup.mk ⟨k, hKG hk⟩ =
        QuotientGroup.mk ⟨k, hKG hk⟩ * QuotientGroup.mk g := hgc.symm
    rw [hgc']
    group
  have h2 := (mk_eq_one_iff_mem_pCoreOf (g * ⟨k, hKG hk⟩ * g⁻¹ * ⟨k, hKG hk⟩⁻¹)).1 h1
  simpa [commutatorElement_def] using h2

end Main

end CFSG.Quasithin.He10
