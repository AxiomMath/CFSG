module

public import CFSG.Quasithin.H13.U3S13473A
public import CFSG.Quasithin.H13.NQS13410H
public import CFSG.Quasithin.H13.U3S132210B

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

theorem inA4_inD6_mem_K4 : ∀ σ : Perm (Fin 6), InA4 σ → InD6 σ → σ ∈ K4L := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_L1T_a6 (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    (L₁Of L (fsuV1 T V) ⊓ T).relIndex (L₁Of L (fsuV1 T V)) = 3 ∧
      L₁Of L (fsuV1 T V) ⊓ T = pCoreOf 2 (L₁Of L (fsuV1 T V)) ∧
      quasithinO2QuotientIso (L₁Of L (fsuV1 T V) ⊔ T) (Perm (Fin 3)) := by
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  have P := s134Plus_L1 S he
  have hTsyl : IsSylowTwoOf T (L₁ ⊔ T) := A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right
  have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
  have hL1N : L₁ ≤ normalizer (fsuV1 T V : Set G) := (oTwoRes_le _).trans inf_le_right
  have hTK : T ≤ normalizer (L₁ : Set G) := s134_T_le_normalizer_L1 S
  obtain ⟨y, hyL1, hyN, hyρ⟩ := s134_exists_mem_L1 S c012_props.1 c012_props.2.1
    c012_props.2.2
  have hKP : ∀ x : ↥(normalizer (V : Set G)), (x : G) ∈ L₁ → S.frame.ρ x ∈ A6.P1sub :=
    fun x hx => inP1_of_pres45 _ (s134_pres45 S x (hL1N hx))
  have hCK : L₁ ⊓ centralizer (V : Set G) ≤ T := P.cent.trans (s134_pCoreOf_L_le_T S)
  have h3 : (L₁ ⊓ T).relIndex L₁ = 3 :=
    s134_relIndex_three S A6.card_P1A6 hL1L hKP hCK hTK hyL1
      (by rw [show (⟨y, S.frame.L_le (hL1L hyL1)⟩ : ↥(normalizer (V : Set G))) =
        ⟨y, hyN⟩ from rfl, hyρ]; exact gens_not_mem.2.2.1)
  have hO : L₁ ⊓ T = pCoreOf 2 L₁ := by
    refine le_antisymm (fun x hx => ?_) (le_inf (pCoreOf_le 2 L₁)
      ((NQS134.s134_pCoreOf_L1_le_R S).trans (NQS134.s134_R_le_T S)))
    have hxN : x ∈ normalizer (V : Set G) := S.frame.L_le (hL1L hx.1)
    exact P.mem_pCoreOf_of_K4 (x := ⟨x, hxN⟩) hx.1 (inA4_inD6_mem_K4 _ (P.rho hx.1)
      (S.frame.T_D ⟨x, hxN⟩ hx.2))
  refine ⟨h3, hO, quot_S3_of_index_three hTsyl (by rw [relIndex_sup_eq hTK, h3]) fun hN => ?_⟩
  have hyT := hN (le_sup_left (b := T) hyL1)
  obtain ⟨hD, hA, hnot⟩ := c012_conj_not_mem
  obtain ⟨t, htT, htσ⟩ := S.frame.DA_T _ hD hA
  have hyt : y * (t : G) * y⁻¹ ∈ T := (mem_normalizer_iff.mp hyT t).mp htT
  have hD' := S.frame.T_D ⟨y * t * y⁻¹, S.frame.T_le hyt⟩ hyt
  apply hnot
  have e : (⟨y * t * y⁻¹, S.frame.T_le hyt⟩ : ↥(normalizer (V : Set G))) =
      ⟨y, hyN⟩ * t * ⟨y, hyN⟩⁻¹ := rfl
  rwa [e, map_mul, map_mul, map_inv, hyρ, htσ] at hD'

theorem s134_L_le_sup (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    L ≤ (L₁Of L (fsuV1 T V) ⊔ T) ⊔ (l2Of S ⊔ T) := by
  set X := (L₁Of L (fsuV1 T V) ⊔ T) ⊔ (l2Of S ⊔ T) with hX
  set Y : Subgroup (Perm (Fin 6)) :=
    ((X ⊓ L).subgroupOf (normalizer (V : Set G))).map S.frame.ρ with hY
  have hCY : A6.P2sub ⊓ alternatingGroup (Fin 6) ≤ Y := by
    intro σ hσ
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 (mem_inf.1 hσ).2
    have hgN2 : (g : G) ∈ normalizer (v2Of S : Set G) :=
      (s134_mem_NV2_iff S g).2 (by rw [hg]; exact (mem_inf.1 hσ).1)
    have hgX : (g : G) ∈ X :=
      mem_sup_right (s134_NLV2_le_L2T S ⟨hgL, hgN2⟩)
    exact ⟨g, mem_subgroupOf.2 ⟨hgX, hgL⟩, hg⟩
  obtain ⟨y, hyL1, hyN, hyρ⟩ := s134_exists_mem_L1 S c012_props.1 c012_props.2.1
    c012_props.2.2
  have hyL : y ∈ L := ((oTwoRes_le _).trans inf_le_left) hyL1
  have hsY : c012 ∈ Y := ⟨⟨y, hyN⟩, mem_subgroupOf.2 ⟨mem_sup_left (mem_sup_left hyL1), hyL⟩,
    hyρ⟩
  have hs1 : Perm.sign c012 = 1 := Perm.mem_alternatingGroup.1 c012_props.1
  have hsC : c012 ∉ A6.P2sub ⊓ alternatingGroup (Fin 6) := fun h =>
    gens_not_mem.1 (mem_inf.1 h).1
  have hA := alt6_le_of_overgroup24 A6.card_P2A6 inf_le_right hCY hsY hs1 hsC
  intro l hl
  set lN : ↥(normalizer (V : Set G)) := ⟨l, S.frame.L_le hl⟩ with hlN
  obtain ⟨g, hg, hgρ⟩ := hA ((S.frame.image_L _).1 ⟨lN, hl, rfl⟩)
  have hgXL := mem_subgroupOf.1 hg
  have hk : S.frame.ρ (g⁻¹ * lN) = 1 := by rw [map_mul, map_inv, hgρ, inv_mul_cancel]
  have hkC : (g : G)⁻¹ * l ∈ L ⊓ centralizer (V : Set G) :=
    ⟨L.mul_mem (L.inv_mem hgXL.2) hl, (s134_rho_eq_one_iff S (g⁻¹ * lN)).1 hk⟩
  have hkT : (g : G)⁻¹ * l ∈ T :=
    s134_pCoreOf_L_le_T S (((s134_centralizer_le_o2Z S).trans (o2Z_le_pCoreOf_of_a6 he)) hkC)
  have := X.mul_mem hgXL.1 (mem_sup_left (mem_sup_right hkT))
  rwa [mul_inv_cancel_left] at this

theorem inH_of_triple (hedge : GoldschmidtEdgeBoundS3) (S : A6.Setting134 G T L V)
    {P₁ P₂ : Subgroup G} (htr : F6.IsGoldschmidtTripleIn (P₁ ⊔ P₂) P₁ P₂)
    (hinf : P₁ ⊓ P₂ = T) : InH T (P₁ ⊔ P₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTP : T ≤ P₁ := hinf ▸ inf_le_left
  refine ⟨hTP.trans le_sup_left, fun hO => ?_⟩
  have htr' := htr.subgroupOf
  have hpc : CFSG.pCore 2 ↥(P₁ ⊔ P₂) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxO : (x : G) ∈ pCoreOf 2 (P₁ ⊔ P₂) := (AppC.mem_pCore_iff_mem_blockQ x).1 hx
    rw [hO, mem_bot] at hxO
    exact Subtype.ext hxO
  have hpc' : Open.pCore 2 ↥(P₁ ⊔ P₂) = ⊥ := by
    exact hpc
  have hb := card_inf_le_of_goldschmidtEdgeBoundS3 hedge ⟨htr', hpc'⟩
  have hT : Nat.card ↥(P₁.subgroupOf (P₁ ⊔ P₂) ⊓ P₂.subgroupOf (P₁ ⊔ P₂)) = Nat.card T := by
    have e : P₁.subgroupOf (P₁ ⊔ P₂) ⊓ P₂.subgroupOf (P₁ ⊔ P₂) =
        (P₁ ⊓ P₂).subgroupOf (P₁ ⊔ P₂) := by
      ext x
      simp only [mem_inf, mem_subgroupOf]
    rw [e, hinf]
    exact Nat.card_congr (subgroupOfEquivOfLe (hTP.trans le_sup_left)).toEquiv
  have := s134_card_T_ge S
  omega

omit [Finite G] in
theorem le_centralizer_of_perfect {L Y : Subgroup G} (hperf : ⁅L, L⁆ = L) (hY : IsCyclic ↥Y)
    (hLY : L ≤ normalizer (Y : Set G)) : L ≤ centralizer (Y : Set G) := by
  let φ : ↥L →* MulAut ↥Y := (conjAct Y).comp (inclusion hLY)
  have hφ : ∀ (l : ↥L) (y : ↥Y), ((φ l y : ↥Y) : G) = l * y * (l : G)⁻¹ := fun l y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ y
  have hker : ⁅L, L⁆ ≤ φ.ker.map L.subtype := by
    rw [commutator_le]
    intro a ha b hb
    refine ⟨⟨⁅a, b⁆, commutator_mem_commutator ha hb |> fun h => hperf ▸ h⟩, ?_, rfl⟩
    show φ _ = 1
    have e : (⟨⁅a, b⁆, hperf ▸ commutator_mem_commutator ha hb⟩ : ↥L) =
        ⁅(⟨a, ha⟩ : ↥L), (⟨b, hb⟩ : ↥L)⁆ := Subtype.ext rfl
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact F6.mulAut_comm_of_isCyclic _ _
  rw [hperf] at hker
  intro l hl
  obtain ⟨l', hl', hll'⟩ := hker hl
  replace hl' : φ l' = 1 := hl'
  refine mem_centralizer_iff.2 fun y hy => ?_
  have h1 := congrArg (fun f : MulAut ↥Y => ((f ⟨y, hy⟩ : ↥Y) : G)) hl'
  simp only [MulAut.one_apply] at h1
  rw [hφ] at h1
  rw [← hll']
  calc y * (l' : G) = (l' : G) * y * (l' : G)⁻¹ * l' := by rw [h1]
    _ = l' * y := by group

theorem s134_false_of_normalizer (S : A6.Setting134 G T L V) {Y₂ : Subgroup G}
    (hY₂M : ¬ Y₂ ≤ normalizer (L : Set G))
    (hcyc : pCoreOf 2 Y₂ = ⊥ → IsCyclic ↥Y₂) (hLN : L ≤ normalizer (Y₂ : Set G))
    (hTN : T ≤ normalizer (Y₂ : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hO : pCoreOf 2 Y₂ = ⊥
  · have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp S.h13.faithful.1.2.1
    have hLC := le_centralizer_of_perfect hperf (hcyc hO) hLN
    apply hY₂M
    intro y hy
    exact centralizer_le_normalizer _ (le_centralizer_iff.1 hLC hy)
  · have hLT : L ⊔ T ≤ normalizer (pCoreOf 2 Y₂ : Set G) :=
      (sup_le hLN hTN).trans (normalizer_le_normalizer_pCoreOf 2 Y₂)
    have hM := s134_normalizer_le_M S hO (pCoreOf_isPGroup 2 Y₂) hLT
    exact hY₂M ((le_normalizer_pCoreOf 2 Y₂).trans hM)

theorem two_pow_odd_mod_three {m : ℕ} (hm : Odd m) : 2 ^ m % 3 = 2 := by
  obtain ⟨r, rfl⟩ := hm
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem comm_mem_of_odd {L₁ : Subgroup G} (h3 : (pCoreOf 2 L₁).relIndex L₁ = 3) {y : G}
    (hyN : y ∈ normalizer (L₁ : Set G)) {m : ℕ} (hm : Odd m) (hym : y ^ m = 1) :
    ∀ l ∈ L₁, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := pCoreOf 2 L₁ with hOdef
  set N := O.subgroupOf L₁ with hN
  have hNn : N.Normal :=
    (normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 L₁)).2 (le_normalizer_pCoreOf 2 L₁)
  have hQ : Nat.card (↥L₁ ⧸ N) = 3 := h3
  have hyO : y ∈ normalizer (O : Set G) := normalizer_le_normalizer_pCoreOf 2 L₁ hyN
  let φ : ↥L₁ →* ↥L₁ :=
    { toFun := fun a => ⟨y * a * y⁻¹, (mem_normalizer_iff.1 hyN a).1 a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφ : ∀ a : ↥L₁, ((φ a : ↥L₁) : G) = y * a * y⁻¹ := fun _ => rfl
  have hφN : N ≤ N.comap φ := fun a ha => by
    rw [mem_comap, hN, mem_subgroupOf, hφ]
    exact (mem_normalizer_iff.1 hyO a).1 (mem_subgroupOf.1 ha)
  let ψ : (↥L₁ ⧸ N) →* (↥L₁ ⧸ N) := QuotientGroup.map N N φ hφN
  have hψ : ∀ a : ↥L₁, ψ (a : ↥L₁ ⧸ N) = ((φ a : ↥L₁) : ↥L₁ ⧸ N) := fun a =>
    QuotientGroup.map_mk N N φ hφN a
  have hcyc : IsCyclic (↥L₁ ⧸ N) := isCyclic_of_prime_card hQ
  obtain ⟨k, hk⟩ := ψ.map_cyclic
  have hq3 : ∀ q : ↥L₁ ⧸ N, q ^ 3 = 1 := fun q => by rw [← hQ]; exact pow_card_eq_one'
  have hk' : ∀ q, ψ q = q ^ (k % 3) := fun q => by rw [hk, zpow_eq_zpow_emod_three (hq3 q)]
  have hkr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ↥L₁ ⧸ N, q₀ ≠ 1 := by
    have : Nontrivial (↥L₁ ⧸ N) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hQ]; norm_num)
    exact exists_ne 1
  have hid : ∀ q, ψ q = q := by
    rcases hkr with h | h | h
    ·
      exfalso
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q₀
      apply hq₀
      have h1 := hk' (a : ↥L₁ ⧸ N)
      rw [h, zpow_zero, hψ, QuotientGroup.eq_one_iff, hN, mem_subgroupOf, hφ] at h1
      rw [QuotientGroup.eq_one_iff, hN, mem_subgroupOf]
      have := (mem_normalizer_iff.1 (inv_mem hyO) _).1 h1
      simpa [mul_assoc] using this
    · intro q
      rw [hk', h, zpow_one]
    ·
      exfalso
      have hpow : ∀ (j : ℕ) (a : ↥L₁), ((⟨y ^ j * a * (y ^ j)⁻¹,
          (mem_normalizer_iff.1 (pow_mem hyN j) a).1 a.2⟩ : ↥L₁) : ↥L₁ ⧸ N) =
            (a : ↥L₁ ⧸ N) ^ (2 ^ j) := by
        intro j
        induction j with
        | zero => intro a; simp
        | succ j ih =>
          intro a
          have e : (⟨y ^ (j + 1) * a * (y ^ (j + 1))⁻¹,
              (mem_normalizer_iff.1 (pow_mem hyN (j + 1)) a).1 a.2⟩ : ↥L₁) =
              φ ⟨y ^ j * a * (y ^ j)⁻¹, (mem_normalizer_iff.1 (pow_mem hyN j) a).1 a.2⟩ := by
            apply Subtype.ext
            show y ^ (j + 1) * (a : G) * (y ^ (j + 1))⁻¹ = y * (y ^ j * a * (y ^ j)⁻¹) * y⁻¹
            rw [pow_succ']
            group
          rw [e, ← hψ, ih, hk', h, pow_succ, pow_mul]
          norm_cast
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q₀
      have h1 := hpow m a
      have e : (⟨y ^ m * a * (y ^ m)⁻¹, (mem_normalizer_iff.1 (pow_mem hyN m) a).1 a.2⟩ : ↥L₁) =
          a := Subtype.ext (by simp [hym])
      rw [e] at h1
      have h2 : ((a : ↥L₁ ⧸ N)) ^ (2 ^ m) = (a : ↥L₁ ⧸ N) ^ 2 := by
        rw [← Nat.mod_add_div (2 ^ m) 3, two_pow_odd_mod_three hm, pow_add, pow_mul,
          hq3, one_pow, mul_one]
      rw [h2, sq] at h1
      apply hq₀
      exact (mul_eq_left.1 h1.symm)
  intro l hl
  have h1 := hid ((⟨l, hl⟩ : ↥L₁) : ↥L₁ ⧸ N)
  rw [hψ, QuotientGroup.eq, hN, mem_subgroupOf] at h1
  have h2 : ((φ ⟨l, hl⟩ : ↥L₁) : G)⁻¹ * l ∈ O := by simpa using h1
  rw [hφ] at h2
  have h3 := inv_mem ((mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 L₁ hl) _).1 h2)
  have e : (l * ((y * l * y⁻¹)⁻¹ * l) * l⁻¹)⁻¹ = y * l * y⁻¹ * l⁻¹ := by group
  rwa [e] at h3

end CFSG.Quasithin.H13.U3
