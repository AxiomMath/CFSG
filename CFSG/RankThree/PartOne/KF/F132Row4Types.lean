module

public import CFSG.RankThree.PartOne.KF.F132DihGen
public import CFSG.RankThree.PartOne.KF.F132LayerData
public import CFSG.RankThree.PartOne.KF.F132KZeroQs
public import CFSG.RankThree.PartOne.KF.F132SL2Torus
public import CFSG.RankThree.PartOne.KF.F132Center
public import CFSG.RankThree.PartOne.KFOUT3.KtyF4Act
public import CFSG.RankThree.PartOne.KFOUT3.KtyF4Ctx
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx
public import CFSG.RankThree.PartOne.KFOUT3.KtyDihCtx
public import CFSG.RankThree.PartOne.KLAY.Frames
public import CFSG.RankThree.PartOne.KF.R4Final
public import CFSG.RankThree.PartOne.KFOUT3.KtyCore
public import CFSG.RankThree.PartOne.KLAY.Sz

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.RankThree.PartOne.KLAY CFSG.RankThree.PartOne.KFOUT3

section Frame

variable {G : Type} [Group G]

theorem exists_r4frame_of [Finite G] {p f : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Core p L A₀ F) (hpq : p ∣ 2 ^ f - 1)
    (hmod : LieModel (L ⧸ Subgroup.center L) .twistedF4 0 2 f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime)
      (hP : F4Param p a K), f = 2 * a + 1 ∧ (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      ∃ ε : ↥L →* ↥(F4.reeGamma K a), IsCentralPQuot p ε ∧
        (∀ t ∈ Tp4 hP, ∃ x : F, ε (Subgroup.inclusion h.F_le x) = t) ∧
        ∀ x : F, ∃ t ∈ Tp4 hP, ε (Subgroup.inclusion h.F_le x) = t := by
  classical
  have hp := h.prime
  have h5 := h.five_le
  rcases hmod with ⟨hcl, -⟩ | ⟨-, hex, -⟩ | ⟨-, -, hree⟩ | ⟨-, ht, -⟩
  · exact absurd hcl (by decide)
  · exact absurd hex (by decide)
  · have hS := ReeTag.large_Ree_model_Schreier (L ⧸ Subgroup.center L) 2 f hree
    obtain ⟨-, a, hfa, K, hKf, hKfin, hK, ⟨e⟩⟩ := hree
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hchar : CharP K ReeTag.F4.prime := by
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by
        rw [Fintype.card_eq_nat_card]
        exact hK)
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
    have hP : F4Param p a K := ⟨hp, h5, hK', by rw [← hfa]; exact hpq⟩
    have hpK : p ∣ Nat.card K - 1 := by rw [hK']; exact hP.dvd
    have hζ := exists_isPrimitiveRoot_of_dvd_card_sub_one hp hpK
    obtain ⟨e'⟩ := hS.2.2.2.2.2 a K hfa hK ⟨e⟩
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
    have hε₀ := isCentralPQuot_center e' hcop
    obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot (MonoidHom.id ↥(F4.reeGamma K a))
      (isCentralPQuot_id p _) _ hε₀ (fun t ht => Tp4_exp hP t ht)
      (fun s hs t ht => Tp4_comm hP s t hs ht)
      (fun X hexp _ => exists_conj_into_Tp4 hP X hexp) h.F_le h.F_exp h.F_comm h.maximal
    exact ⟨a, K, hKf, hKfin, hchar, hP, hfa, hζ, ε, hε, hFT₁, hFT₂⟩
  · exact absurd ht (by decide)

theorem row4_wctx {p a : ℕ} {L F : Subgroup G} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hP : F4Param p a K) (hFL : F ≤ L) (hFexp : ∀ x ∈ F, x ^ p = 1)
    (ε : ↥L →* ↥(F4.reeGamma K a)) (hε : IsCentralPQuot p ε)
    (hFT₁ : ∀ t ∈ Tp4 hP, ∃ x : F, ε (Subgroup.inclusion hFL x) = t)
    (hFT₂ : ∀ x : F, ∃ t ∈ Tp4 hP, ε (Subgroup.inclusion hFL x) = t) :
    ∃ S : WCtx (f4Act (K := K) hP.theta_dvd) L F,
      ∀ d, ε (Subgroup.inclusion hFL (S.tor d)) = tp4M hP d := by
  classical
  have hp := hP.prime
  have h5 := hP.five_le
  have hθ := hP.theta_dvd
  obtain ⟨SM, hSM⟩ := exists_wctx_f4' hP (f4tau p K (2 ^ a)) (fun i b => tp4Hom_f4tau hP.card i b)
  have hVexp : ∀ d : G2V p K, d ^ p = 1 := fun d =>
    funext fun i => Subtype.ext (by simpa using (mem_rootsOfUnity p _).mp (d i).2)
  obtain ⟨S₁, hrel₁⟩ := wctx_ofCentralQuot' hVexp SM (MonoidHom.id _) (isCentralPQuot_id p _) ε hε
    hFL hFexp hFT₁ hFT₂
  have hmem : ∀ γ : DihedralGroup 8, f4Act (K := K) hθ γ ∈
      Subgroup.closure (Set.range (f4tau p K (2 ^ a))) := by
    intro γ
    rw [range_f4tau]
    exact pairAct_mem_closure f4s1_mul_self f4s2_mul_self (f4_braid hθ) γ
  let f₁ : DihedralGroup 8 →* ↥(Subgroup.closure (Set.range (f4tau p K (2 ^ a)))) :=
    (f4Act (K := K) hθ).codRestrict _ hmem
  have hf₁ : Function.Surjective f₁ := by
    rintro ⟨x, hx⟩
    rw [range_f4tau] at hx
    obtain ⟨γ, hγ⟩ := exists_pairAct_of_mem_closure (by decide) f4s1_mul_self f4s2_mul_self
      (f4_braid hθ) hx
    exact ⟨γ, Subtype.ext hγ⟩
  let S := wctxPull (act := f4Act (K := K) hθ) f₁ hf₁ (fun γ => rfl) S₁
  refine ⟨S, fun d => ?_⟩
  show ε (Subgroup.inclusion hFL (S₁.tor d)) = _
  rw [hrel₁ d, hSM d]
  rfl

end Frame

section Layers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem row4_layer0 (h : Sec12Hyp G p A c L E)
    (hEA : E = A) (hEeq : E = (E ⊓ L) ⊔ Subgroup.zpowers c)
    {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hP : F4Param p a K)
    (ε : ↥L →* ↥(F4.reeGamma K a)) (hε : IsCentralPQuot p ε)
    (S : WCtx (f4Act (K := K) hP.theta_dvd) L (E ⊓ L))
    (hrel : ∀ d, ε (Subgroup.inclusion inf_le_right (S.tor d)) = tp4M hP d)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (Tp4 hP).map (MonoidHom.id ↥(F4.reeGamma K a)))
    {z : rootsOfUnity p K} (hz : IsPrimitiveRoot (z : Kˣ) p) :
    ∃ K₀ : Subgroup G, LayerCore p A L ((S.tor ![z, z ^ 2] : ↥(E ⊓ L)) : G) K₀ ∧
      StatedClassicalModel (↥K₀ ⧸ Subgroup.center ↥K₀) .PSL 2 2 (2 * a + 1) := by
  classical
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := Sec12Three.five_le h; omega
  have hK := hP.card
  have hchar : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hz1 : z ≠ 1 := g2v_ne_one_of_primitive hp.one_lt hz
  have hSL := f4_SL2Torus hP hz
  have hD := f4_layerD hP (z := z) (z2 := z ^ 2) hz rfl
  have hbA : ((S.tor ![z, z ^ 2] : ↥(E ⊓ L)) : G) ∈ A := hEA ▸ (S.tor ![z, z ^ 2]).2.1
  have hbL : ((S.tor ![z, z ^ 2] : ↥(E ⊓ L)) : G) ∈ L := (S.tor ![z, z ^ 2]).2.2
  have hb1 : ((S.tor ![z, z ^ 2] : ↥(E ⊓ L)) : G) ≠ 1 := by
    intro h1
    have h2 : S.tor ![z, z ^ 2] = 1 := Subtype.ext h1
    have h3 : (![z, z ^ 2] : G2V p K) = 1 := (map_eq_one_iff S.tor S.tor.injective).1 h2
    exact hz1 (by simpa using congrFun h3 0)
  have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    calc A = E := hEA.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := hEeq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  have h1a := hP.one_le
  exact layerCore_of_SL2Torus hp hp2 (IsPGroup.of_card h.A_card) h.A_elem
    h.L_le_centralizer hA ε (MonoidHom.id ↥(F4.reeGamma K a)) hε (isCentralPQuot_id p _) hbA hbL hb1
    (Tp4_exp hP _ (tp4M_mem_Tp4 hP _)) (hrel ![z, z ^ 2]) hAT hK (by omega) ⟨(z : Kˣ), hz⟩ hSL hD

end Layers

section Suzuki

open CFSG.LieType.Ree.LargeReeCover CFSG.LieType.Ree.LargeReeInvolution

theorem exists_noncomm_of_perfect {D : Type*} [Group D] [Nontrivial D] (hperf : Group.IsPerfect D) :
    ∃ a b : D, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hc : commutator D ≤ ⊥ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    simp [commutatorElement_def, hcon g₁ g₂]
  obtain ⟨x, hx⟩ := exists_ne (1 : D)
  have hx' : x ∈ commutator D := hperf.1 ▸ Subgroup.mem_top x
  exact hx (Subgroup.mem_bot.1 (hc hx'))

theorem center_eq_bot_of_simple_perfect {D : Type*} [Group D] (hs : IsSimpleGroup D)
    (hperf : Group.IsPerfect D) : Subgroup.center D = ⊥ := by
  have := hs
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_perfect hperf
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center D) with h | h
  · exact h
  · exfalso
    have ha : a ∈ Subgroup.center D := h ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha) b).symm

theorem isQuasisimple_of_simple_perfect {D : Type*} [Group D] (hs : IsSimpleGroup D)
    (hperf : Group.IsPerfect D) : IsQuasisimple D := by
  have := hs
  have hZ := center_eq_bot_of_simple_perfect hs hperf
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_perfect hperf
  let e : D ⧸ Subgroup.center D ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, e.isSimpleGroup, e.symm a, e.symm b, fun h => hab ?_⟩
  simpa using congrArg e h

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {p : ℕ}

theorem tp4M_one_mem_block (hP : F4Param p a K) (z : rootsOfUnity p K) :
    tp4M hP ![1, z] ∈ (F4.reeLocalBlock K a blk2).subgroupOf (F4.reeGamma K a) := by
  rw [Subgroup.mem_subgroupOf, coe_tp4M, tp4Hom_apply]
  have h1 : torusPair (K := K) a (1, ((z : rootsOfUnity p K) : Kˣ)) =
      pairedTorusHom (K := K) a (f4i 1) (f4i 2) ((z : rootsOfUnity p K) : Kˣ) := by
    rw [torusPair_apply, pairedTorusHom_apply]
    simp [torusElt_one]
  have h2 : torusPair (K := K) a ((((![1, z] : G2V p K) 0 : rootsOfUnity p K) : Kˣ),
      (((![1, z] : G2V p K) 1 : rootsOfUnity p K) : Kˣ)) =
      torusPair (K := K) a (1, ((z : rootsOfUnity p K) : Kˣ)) := by simp
  rw [h2, h1, reeLocalBlock_eq_rankOneGroupTwo hP.one_le hP.card]
  exact Subgroup.subset_closure (Or.inl (Or.inr ⟨((z : rootsOfUnity p K) : Kˣ), rfl⟩))

theorem card_Tp4_inf_block (hP : F4Param p a K) {z z2 : rootsOfUnity p K}
    (hz : IsPrimitiveRoot (z : Kˣ) p) (hz2 : (z2 : Kˣ) = (z : Kˣ) ^ (1 + 2 ^ a)) :
    Nat.card ↥(Tp4 hP ⊓ (F4.reeLocalBlock K a blk2).subgroupOf (F4.reeGamma K a)) = p := by
  classical
  have hK := hP.card
  have hp := hP.prime
  have : Fact p.Prime := ⟨hp⟩
  have hz1 : z ≠ 1 := g2v_ne_one_of_primitive hp.one_lt hz
  have hfacts := reeLocalBlock_subgroupOf_facts (K := K) (a := a) hP.one_le hK
  set D' : Subgroup ↥(F4.reeGamma K a) := (F4.reeLocalBlock K a blk2).subgroupOf (F4.reeGamma K a)
    with hD'
  have hZ : Subgroup.center ↥D' = ⊥ := center_eq_bot_of_simple_perfect hfacts.1 hfacts.2.1
  have hD : layerD (tp4M hP ![z, z2]) = D' := f4_layerD_sz hP hz hz2
  set m : ↥(F4.reeGamma K a) := tp4M hP ![z, z2] with hm
  have hv1 : (![z, z2] : G2V p K) ≠ 1 := fun h1 => hz1 (by simpa using congrFun h1 0)
  have hm1 : m ≠ 1 := fun h1 => hv1 (tp4M_injective hP (h1.trans (map_one _).symm))
  have hDle : ∀ d ∈ D', d * m = m * d := by
    intro d hd
    have hd' : d ∈ layerD m := hD ▸ hd
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hd'
    exact Subgroup.mem_centralizer_singleton_iff.1 y.2
  have hmD : m ∉ D' := by
    intro hmD
    have hc : (⟨m, hmD⟩ : ↥D') ∈ Subgroup.center ↥D' := by
      rw [Subgroup.mem_center_iff]
      intro d
      apply Subtype.ext
      exact hDle d d.2
    rw [hZ, Subgroup.mem_bot] at hc
    exact hm1 (congrArg Subtype.val hc)
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨(z : Kˣ), hz⟩
  have hcard2 : Nat.card ↥(Tp4 hP) = p ^ 2 := by
    rw [Tp4, Nat.card_congr (MonoidHom.ofInjective (tp4M_injective hP)).toEquiv.symm]
    exact card_G2V hp.pos hζex
  set u : ↥(F4.reeGamma K a) := tp4M hP ![1, z] with hu
  have hvu : (![1, z] : G2V p K) ≠ 1 := fun h1 => hz1 (by simpa using congrFun h1 1)
  have hu1 : u ≠ 1 := fun h1 => hvu (tp4M_injective hP (h1.trans (map_one _).symm))
  have hup : u ^ p = 1 := Tp4_exp hP u (tp4M_mem_Tp4 hP _)
  have huT : u ∈ Tp4 hP := tp4M_mem_Tp4 hP _
  have huD : u ∈ D' := tp4M_one_mem_block hP z
  have horder : orderOf u = p := orderOf_eq_prime hup hu1
  have hdvd : p ∣ Nat.card ↥(Tp4 hP ⊓ D') := by
    have := Subgroup.orderOf_dvd_natCard (Tp4 hP ⊓ D') (x := u) ⟨huT, huD⟩
    rwa [horder] at this
  have hle : Nat.card ↥(Tp4 hP ⊓ D') ∣ p ^ 2 := hcard2 ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow hp).1 hle
  have hi1 : i = 1 := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [hci, pow_zero] at hdvd
      exact absurd (Nat.dvd_one.1 hdvd) hp.ne_one
    · rfl
    · exfalso
      have heq : Tp4 hP ⊓ D' = Tp4 hP :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hci, hcard2])
      have hmT : m ∈ Tp4 hP := tp4M_mem_Tp4 hP _
      have hmT' : m ∈ Tp4 hP ⊓ D' := by rw [heq]; exact hmT
      exact hmD hmT'.2
  rw [hci, hi1, pow_one]

theorem row4_layerSz {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hP : F4Param p a K)
    (ε : ↥L →* ↥(F4.reeGamma K a)) (hε : IsCentralPQuot p ε)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (Tp4 hP).map (MonoidHom.id ↥(F4.reeGamma K a)))
    {z z2 : rootsOfUnity p K} (hz : IsPrimitiveRoot (z : Kˣ) p)
    (hz2 : (z2 : Kˣ) = (z : Kˣ) ^ (1 + 2 ^ a))
    {x : G} (hxA : x ∈ A) (hxL : x ∈ L) (hb : ε ⟨x, hxL⟩ = tp4M hP ![z, z2]) :
    x ≠ 1 ∧ IsQuasisimple ↥(kLayer L x) ∧ ¬ p ∣ Nat.card (Subgroup.center ↥(kLayer L x)) ∧
      Nat.card ↥(A ⊓ kLayer L x) = p ∧
      (Function.Injective ε → Subgroup.center ↥(kLayer L x) = ⊥ ∧
        Nat.card ↥(kLayer L x) =
          (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) ∧
        Nonempty (↥(kLayer L x) ≃* suzukiGroup a K)) := by
  classical
  have hK := hP.card
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hz1 : z ≠ 1 := g2v_ne_one_of_primitive hp.one_lt hz
  have hfacts := reeLocalBlock_subgroupOf_facts (K := K) (a := a) hP.one_le hK
  set D' : Subgroup ↥(F4.reeGamma K a) := (F4.reeLocalBlock K a blk2).subgroupOf (F4.reeGamma K a)
    with hD'
  have hZ : Subgroup.center ↥D' = ⊥ := center_eq_bot_of_simple_perfect hfacts.1 hfacts.2.1
  have hDD : inSubgroup perfectResidual (Subgroup.centralizer
      ({tp4M hP ![z, z2]} : Set ↥(F4.reeGamma K a))) = D' := f4_layerD_sz hP hz hz2
  set m : ↥(F4.reeGamma K a) := tp4M hP ![z, z2] with hm
  have hv1 : (![z, z2] : G2V p K) ≠ 1 := fun h1 => hz1 (by simpa using congrFun h1 0)
  have hm1 : m ≠ 1 := fun h1 => hv1 (tp4M_injective hP (h1.trans (map_one _).symm))
  have hmp : m ^ p = 1 := Tp4_exp hP m (tp4M_mem_Tp4 hP _)
  have hqs : IsQuasisimple ↥D' := isQuasisimple_of_simple_perfect hfacts.1 hfacts.2.1
  have hKq : IsQuasisimple ↥(inSubgroup perfectResidual (Subgroup.centralizer
      ({m} : Set ↥(F4.reeGamma K a)))) := by
    rw [hDD]
    exact hqs
  have hKz : ¬ p ∣ Nat.card (Subgroup.center ↥(inSubgroup perfectResidual (Subgroup.centralizer
      ({m} : Set ↥(F4.reeGamma K a))))) := by
    rw [hDD, hZ, Subgroup.card_bot]
    exact hp.not_dvd_one
  have hTK : Nat.card ↥(Tp4 hP ⊓ inSubgroup perfectResidual (Subgroup.centralizer
      ({m} : Set ↥(F4.reeGamma K a)))) = p := by
    rw [hDD]
    exact card_Tp4_inf_block hP hz hz2
  have hx1 : x ≠ 1 := by
    intro h1
    apply hm1
    rw [← hb]
    have : (⟨x, hxL⟩ : ↥L) = 1 := Subtype.ext h1
    rw [this, map_one]
  have := h.A_elem
  obtain ⟨K₀, hK₀eq, hqs', hz', hAK, -, hiso⟩ := layerData_of_cover hp h.A_elem ε
    (MonoidHom.id ↥(F4.reeGamma K a)) hε (isCentralPQuot_id p _) hxA hxL hmp hb
    (T₀ := Tp4 hP) (fun t ht => Tp4_exp hP t ht) hAT hKq hKz hTK
  subst hK₀eq
  refine ⟨hx1, hqs', hz', hAK, fun hεi => ?_⟩
  obtain ⟨eKD⟩ := hiso hεi (fun u v huv => huv)
  let eD : ↥D' ≃* suzukiGroup a K :=
    ((Subgroup.subgroupOfEquivOfLe (reeLocalBlock_le_reeGamma blk2)).trans
      (MulEquiv.subgroupCongr (reeLocalBlock_eq_rankOneGroupTwo hP.one_le hK))).trans
      (rankOneEquivSuzuki K a hP.one_le hK)
  let e₁ : ↥(kLayer L x) ≃* ↥D' := eKD.trans (MulEquiv.subgroupCongr hDD)
  refine ⟨?_, ?_, ⟨e₁.trans eD⟩⟩
  · apply Subgroup.eq_bot_of_card_eq
    rw [card_center_mulEquiv e₁, hZ, Subgroup.card_bot]
  · rw [Nat.card_congr e₁.toEquiv]
    exact hfacts.2.2

end Suzuki

section Numerics

theorem sz_psu_arith {a f' d : ℕ} (hf' : 1 ≤ f') (hd : d = 1 ∨ d = 3)
    (h : (2 ^ f') ^ 3 * (((2 ^ f') ^ 2 - 1) * ((2 ^ f') ^ 3 + 1)) =
      d * ((2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1))) :
    False := by
  have hq'2 : 2 ≤ 2 ^ f' := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f' := Nat.pow_le_pow_right (by norm_num) hf'
  have hq2 : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq'ev : Even (2 ^ f') := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hqev : Even (2 ^ (2 * a + 1)) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hO₁ : Odd (((2 ^ f') ^ 2 - 1) * ((2 ^ f') ^ 3 + 1)) := by
    refine Odd.mul ?_ ?_
    · have h4 : 1 ≤ (2 ^ f') ^ 2 := Nat.one_le_pow _ _ (by omega)
      have hev : Even ((2 ^ f') ^ 2) := (Nat.even_pow.2 ⟨hq'ev, by norm_num⟩)
      rcases hev with ⟨r, hr⟩
      exact ⟨r - 1, by omega⟩
    · have hev : Even ((2 ^ f') ^ 3) := (Nat.even_pow.2 ⟨hq'ev, by norm_num⟩)
      rcases hev with ⟨r, hr⟩
      exact ⟨r, by omega⟩
  have hO₂ : Odd (d * ((2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1))) := by
    refine Odd.mul ?_ (Odd.mul ?_ ?_)
    · rcases hd with rfl | rfl
      · exact odd_one
      · exact ⟨1, rfl⟩
    · rcases hqev with ⟨r, hr⟩
      exact ⟨r - 1, by omega⟩
    · have hev : Even ((2 ^ (2 * a + 1)) ^ 2) := (Nat.even_pow.2 ⟨hqev, by norm_num⟩)
      rcases hev with ⟨r, hr⟩
      exact ⟨r, by omega⟩
  set O₁ := ((2 ^ f') ^ 2 - 1) * ((2 ^ f') ^ 3 + 1) with hO₁def
  set O₂ := d * ((2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)) with hO₂def
  have hpow1 : (2 ^ f') ^ 3 = 2 ^ (3 * f') := by rw [← pow_mul, mul_comm]
  have hpow2 : (2 ^ (2 * a + 1)) ^ 2 = 2 ^ (2 * (2 * a + 1)) := by rw [← pow_mul, mul_comm]
  have hE : 2 ^ (3 * f') * O₁ = 2 ^ (2 * (2 * a + 1)) * O₂ := by
    rw [← hpow1, ← hpow2]
    calc (2 ^ f') ^ 3 * O₁ = (2 ^ f') ^ 3 * (((2 ^ f') ^ 2 - 1) * ((2 ^ f') ^ 3 + 1)) := rfl
      _ = d * ((2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)) := h
      _ = (2 ^ (2 * a + 1)) ^ 2 * O₂ := by rw [hO₂def]; ring
  have hc₁ : Nat.Coprime (2 ^ (3 * f')) O₂ := (Nat.coprime_two_left.2 hO₂).pow_left _
  have hc₂ : Nat.Coprime (2 ^ (2 * (2 * a + 1))) O₁ := (Nat.coprime_two_left.2 hO₁).pow_left _
  have hle₁ : 3 * f' ≤ 2 * (2 * a + 1) := by
    have hdvd : 2 ^ (3 * f') ∣ 2 ^ (2 * (2 * a + 1)) * O₂ := ⟨O₁, hE.symm⟩
    have := hc₁.dvd_of_dvd_mul_right hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  have hle₂ : 2 * (2 * a + 1) ≤ 3 * f' := by
    have hdvd : 2 ^ (2 * (2 * a + 1)) ∣ 2 ^ (3 * f') * O₁ := ⟨O₂, hE⟩
    have := hc₂.dvd_of_dvd_mul_right hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  have hm : 3 * f' = 2 * (2 * a + 1) := le_antisymm hle₁ hle₂
  rw [hm] at hE
  have hOO : O₁ = O₂ := Nat.eq_of_mul_eq_mul_left (by positivity) hE
  obtain ⟨m, hm1, hm2⟩ : ∃ m, f' = 2 * m ∧ 2 * a + 1 = 3 * m := ⟨f' / 2, by omega, by omega⟩
  have hm1' : 1 ≤ m := by omega
  set x : ℕ := 2 ^ m with hx
  have hx2 : 2 ≤ x := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1'
  have hq' : 2 ^ f' = x ^ 2 := by rw [hm1, pow_mul', hx]
  have hq : 2 ^ (2 * a + 1) = x ^ 3 := by rw [hm2, pow_mul', hx]
  rw [hO₁def, hO₂def] at hOO
  rw [hq', hq] at hOO
  have hx6 : (x ^ 2) ^ 3 = (x ^ 3) ^ 2 := by ring
  have hpos : 0 < (x ^ 3) ^ 2 + 1 := by positivity
  have hOO' : ((x ^ 2) ^ 2 - 1) * ((x ^ 3) ^ 2 + 1) = d * (x ^ 3 - 1) * ((x ^ 3) ^ 2 + 1) := by
    calc ((x ^ 2) ^ 2 - 1) * ((x ^ 3) ^ 2 + 1) = ((x ^ 2) ^ 2 - 1) * ((x ^ 2) ^ 3 + 1) := by
          rw [hx6]
      _ = d * ((x ^ 3 - 1) * ((x ^ 3) ^ 2 + 1)) := hOO
      _ = d * (x ^ 3 - 1) * ((x ^ 3) ^ 2 + 1) := by ring
  have hcan := Nat.eq_of_mul_eq_mul_right hpos hOO'
  set y : ℕ := x ^ 3 with hy
  have hy1 : 1 ≤ y := Nat.one_le_pow _ _ (by omega)
  have hxy : (x ^ 2) ^ 2 = x * y := by rw [hy]; ring
  rw [hxy] at hcan
  have hxy2 : 2 * y ≤ x * y := Nat.mul_le_mul_right y hx2
  rcases hd with rfl | rfl
  · omega
  · by_cases hx3 : x = 2
    · have hy8 : y = 8 := by rw [hy, hx3]; norm_num
      rw [hx3, hy8] at hcan
      omega
    · have hx3' : 3 ≤ x := by omega
      have hxy3 : 3 * y ≤ x * y := Nat.mul_le_mul_right y hx3'
      omega

theorem card_psu3_mul_gcd {F : Type} [Field F] [Finite F] {f' : ℕ} (hf' : 1 ≤ f')
    (hF : Nat.card F = (2 ^ f') ^ 2) :
    Nat.gcd 3 (2 ^ f' + 1) * Nat.card (StatedProj (StatedSU 3 (2 ^ f') F)) =
      (2 ^ f') ^ 3 * (((2 ^ f') ^ 2 - 1) * ((2 ^ f') ^ 3 + 1)) := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hf' hF (n := 3)
    (by norm_num)
  have hIcc : Finset.Icc 2 3 = {2, 3} := by decide
  have h3 : 3 * (3 - 1) / 2 = 3 := by norm_num
  rw [hIcc, Finset.prod_insert (by decide), Finset.prod_singleton, h3] at h
  have hq2le : 1 ≤ (2 ^ f') ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hA : (((2 ^ f' : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = (2 ^ f') ^ 2 - 1 := by
    have : (((2 ^ f' : ℕ) : ℤ) ^ 2 - (-1) ^ 2) = (((2 ^ f') ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hq2le]
      ring
    rw [this, Int.toNat_natCast]
  have hB : (((2 ^ f' : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = (2 ^ f') ^ 3 + 1 := by
    have : (((2 ^ f' : ℕ) : ℤ) ^ 3 - (-1) ^ 3) = (((2 ^ f') ^ 3 + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [this, Int.toNat_natCast]
  rw [hA, hB] at h
  have hddvd : Nat.gcd 3 (2 ^ f' + 1) ∣ (2 ^ f') ^ 3 * (((2 ^ f') ^ 2 - 1) * ((2 ^ f') ^ 3 + 1)) := by
    have h1 : 2 ^ f' + 1 ∣ (2 ^ f') ^ 3 + 1 := by
      simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ f') 1 (by decide : Odd 3)
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left
      (Nat.dvd_trans (Nat.gcd_dvd_right 3 (2 ^ f' + 1)) h1) _) _
  rw [h]
  exact Nat.mul_div_cancel' hddvd

theorem not_psu_three_of_suzuki {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) {a : ℕ}
    (hcard : Nat.card X =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)) (f' : ℕ) :
    ¬ StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 f' := by
  rintro ⟨hadm, F, hFf, hFfin, hF, ⟨e⟩⟩
  have hf' : 1 ≤ f' := hadm.2.1
  have hcardeq : Nat.card (StatedProj (StatedSU 3 (2 ^ f') F)) = Nat.card X := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_congr
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv]
  have h := card_psu3_mul_gcd hf' hF
  rw [hcardeq, hcard] at h
  have hd : Nat.gcd 3 (2 ^ f' + 1) = 1 ∨ Nat.gcd 3 (2 ^ f' + 1) = 3 :=
    (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 _)
  exact sz_psu_arith hf' hd h.symm

end Numerics

section SzAt

variable {G : Type} [Group G]

@[expose] def SzAt (p : ℕ) (E : Subgroup G) (f : ℕ) (t : MulAut E) : Prop :=
  (¬ ∃ f' : ℕ, kExceptional p (kZero p E t) f') ∧ LieModel ↥(kZero p E t) .twistedB2 0 2 f ∧
    autMovedInG E t ≤ kZero p E t

theorem SzAt.conj {p f : ℕ} {E : Subgroup G} {t : MulAut E} (h : SzAt p E f t) {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    SzAt p E f (conjAut E w hw * t * (conjAut E w hw)⁻¹) := by
  obtain ⟨hne, hmod, hmov⟩ := h
  have hK := kZero_conj p t hw
  refine ⟨?_, ?_, ?_⟩
  · rw [hK]
    rintro ⟨f', hf'⟩
    exact hne ⟨f', (Equivariance.kExceptional_conjBy_iff p f' w (kZero p E t)).mp hf'⟩
  · rw [hK]
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      ((kZero p E t).equivMapOfInjective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective) hmod
  · rw [hK, Equivariance.autMovedInG_conj t hw]
    exact Subgroup.map_mono hmov

end SzAt

@[expose] def TwistedF4CenterBot : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → ∀ f : ℕ, 1 ≤ f →
    LieModel (X ⧸ Subgroup.center X) .twistedF4 0 2 f → Subgroup.center X = ⊥

theorem card_multiplier_twistedF4 (f : ℕ) :
    Nat.card (Blueprint.Multiplier.generic .twistedF4 0 2 f ×
      Blueprint.Multiplier.exceptional .twistedF4 0 2 f) = 1 := by
  have hgen : Blueprint.Multiplier.genericOrders .twistedF4 0 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.genericOrders
    rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .twistedF4 0 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem twistedF4CenterBot_of_bridge
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hBr : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f →
      CFSG.Models.LieModel X .twistedF4 0 2 f) : TwistedF4CenterBot :=
  fun _ _ _ hqs f _ hm => CFSG.RankThree.PartOne.KF132.center_eq_bot_of_multiplier hGA hqs
    (hBr _ f hm) (card_multiplier_twistedF4 f)

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

theorem kf132Row4_classes (hGA : CFSG.Open.GriessAllModelsStatement)
    (hF4 : TwistedF4CenterBot) (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hEA : E = A) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hmod : LieModel (L ⧸ Subgroup.center L) .twistedF4 0 2 f) :
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → KFAt p E f t ∨ SzAt p E f t := by
  classical
  subst hEA
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hZL : Subgroup.center L = ⊥ := hF4 L hF.isQuasisimple_L f hf1 hmod
  have hG : Sec12TwoGeneric p c L E := sec12TwoGeneric_of_center_bot hF hZL
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have R : Sec12Three.Restr c L E (E ⊓ L) := h.restr_of_generic hG
  have hcore : Table123Core p L (E ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨a, K, hKf, hKfin, hchar, hP, hfa, ⟨ζ, hζ⟩, ε, hε, hFT₁, hFT₂⟩ :=
    exists_r4frame_of hcore hpq hmod
  have hθ := hP.theta_dvd
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨ζ, hζ⟩
  obtain ⟨S, hrel⟩ := row4_wctx hP hcore.F_le hcore.F_exp ε hε hFT₁ hFT₂
  have hAT : ((E ⊓ L).subgroupOf L).map ε =
      (Tp4 hP).map (MonoidHom.id ↥(F4.reeGamma K a)) := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  have hεinj : Function.Injective ε := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have := hε.central (MonoidHom.mem_ker.2 hx)
    rw [hZL, Subgroup.mem_bot] at this
    exact this
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  let z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p ζ).2 hζp⟩
  have hz : IsPrimitiveRoot (z : Kˣ) p := hζ
  let z2 : rootsOfUnity p K := z ^ (1 + 2 ^ a)
  have hz2 : (z2 : Kˣ) = (z : Kˣ) ^ (1 + 2 ^ a) := rfl
  have hp1 := hP.one_le
  have hg3 : 3 ≤ 2 * a + 1 := by omega
  obtain ⟨K₀, hd₀, hm₀⟩ := row4_layer0 h rfl hG.E_eq hP ε hε S hrel hAT hz
  have hinjF := actF_injective_of_inj S (f4Act_injective hp h5 hζex hθ)
  have hconj := exists_dihedral_conj_parity (n := 8) (Or.inr (Or.inr rfl))
  have hone : (1 : ZMod 8).val = 1 := rfl
  have hmov0 : Nat.card (movedV (f4Act (K := K) hθ (DihedralGroup.sr 0))) = p := by
    rw [f4Act_sr_zero]
    exact card_movedV_f4s1 hp h5 hζex
  have hmov1 : Nat.card (movedV (f4Act (K := K) hθ (DihedralGroup.sr 1))) = p := by
    rw [f4Act_sr_one]
    exact card_movedV_f4s2 hp h5 hζex
  obtain ⟨t₀, ht₀L, hr₀, hw₀⟩ := exists_engine_reflection (p := p) S R hinjF 0
    (isAutReflection_actF_sr S hinjF 0 hmov0)
  obtain ⟨t₁, ht₁L, hr₁, hw₁⟩ := exists_engine_reflection (p := p) S R hinjF 1
    (isAutReflection_actF_sr S hinjF 1 hmov1)
  have hrs₀ : t₀ ∈ reflectionSet p E := ⟨hr₀, L, hF13.inZeroStar, ht₀L⟩
  have hrs₁ : t₁ ∈ reflectionSet p E := ⟨hr₁, L, hF13.inZeroStar, ht₁L⟩
  have hv₀ : f4Act (K := K) hθ (DihedralGroup.sr 0) ![z, z ^ 2] = ![z, z ^ 2] := by
    rw [f4Act_sr_zero]
    refine g2v_ext ?_ ?_
    · rw [f4s1_apply_zero]
      simp [pow_two]
    · rw [f4s1_apply_one]
  have hv₁ : f4Act (K := K) hθ (DihedralGroup.sr 1) ![z, z2] = ![z, z2] := by
    rw [f4Act_sr_one]
    refine g2v_ext ?_ ?_
    · rw [f4s2_apply_zero]
    · rw [f4s2_apply_one]
      have e : z ^ (2 * 2 ^ a + 2) = z2 * z2 := by
        simp only [z2]
        rw [← pow_add]
        congr 1
        ring
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [e, mul_inv_cancel_right]
  have hfix₀ := fix_of_weylG_fix S R hinjF ht₀L ![z, z ^ 2] (by rw [hw₀]; exact hv₀)
  have hfix₁ := fix_of_weylG_fix S R hinjF ht₁L ![z, z2] (by rw [hw₁]; exact hv₁)
  have hx₀E : ((S.tor ![z, z ^ 2] : ↥(E ⊓ L)) : G) ∈ E := R.F_le_E (S.tor _).2
  have hx₁E : ((S.tor ![z, z2] : ↥(E ⊓ L)) : G) ∈ E := R.F_le_E (S.tor _).2
  have hx₁L : ((S.tor ![z, z2] : ↥(E ⊓ L)) : G) ∈ L := (S.tor ![z, z2]).2.2
  have hx₁A : ((S.tor ![z, z2] : ↥(E ⊓ L)) : G) ∈ E := hx₁E
  have hKF₀ : KFAt p E (2 * a + 1) t₀ :=
    kfAt_of_core_refl hGA h rfl hcL hd₀ hg3 hm₀ hr₀ ht₀L (hF13.reflection t₀ hrs₀) hx₀E hfix₀
  obtain ⟨hx₁1, hqs₁, hz₁, hAK₁, hiso₁⟩ := row4_layerSz h hP ε hε hAT hz hz2 hx₁A hx₁L
    (hrel ![z, z2])
  obtain ⟨hZK₁, hcard₁, ⟨eSz⟩⟩ := hiso₁ hεinj
  have hE3 : Nat.card E = p ^ 3 := h.A_card
  have hAK₁' : Nat.card ↥(E ⊓ kLayer L ((S.tor ![z, z2] : ↥(E ⊓ L)) : G)) = p := hAK₁
  have hK1 := kZero_eq_of_layer_qs h hE3 h.L_le_centralizer hcL hr₁ ht₁L (hF13.reflection t₁ hrs₁)
    hx₁E hx₁L hx₁1 hfix₁ hAK₁' hqs₁ hz₁
  have hSz₁ : SzAt p E (2 * a + 1) t₁ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hK1.1]
      rintro ⟨f', -, -, hmodel'⟩
      exact not_psu_three_of_suzuki hZK₁ hcard₁ f' hmodel'
    · rw [hK1.1]
      refine Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, a, hp1, K, hKf, hKfin, rfl, ?_, ⟨eSz⟩⟩))
      rw [hP.card]
    · rw [hK1.1]
      exact hK1.2.1
  subst hfa
  intro s hs hsL
  obtain ⟨i, hi⟩ := exists_sr_of_reflection S R hinjF (f4Act_refl hp h5 hζex hθ) hsL hs.1
  have hpar : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  rcases hpar with hpar | hpar
  · exact Or.inl (kfAt_of_parity_G S R hinjF (MulEquiv.refl _) hconj hw₀ hi
      (by rw [ZMod.val_zero]; omega) hKF₀)
  · obtain ⟨x, hxL, hxE, hx⟩ := exists_conj_of_parity_G S R hinjF (MulEquiv.refl _) hconj hw₁ hi
      (by rw [hone]; omega)
    rw [hx]
    exact Or.inr (hSz₁.conj hxE)

end Main

end CFSG.RankThree.PartOne.KF132

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KF132 CFSG.RankThree.PartOne.KFU
  CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem kf132Types_row4
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hF4 : TwistedF4CenterBot) : KF132Types 4 := by
  intro G _ _ p A c L E h hF hF13 hT hrow hrA hr9 t ht htL KS hKS
  have hEA : E = A := hrA (by norm_num)
  obtain ⟨f, hf1, hpq, hmod⟩ := hrow
  have hall := kf132Row4_classes hGA hF4 h hF hF13 hEA hf1 hpq hmod
  refine ⟨f, ⟨hf1, hpq, hmod⟩, ?_, fun _ => ?_⟩
  · rcases hall t ht htL with hKF | hSz
    · have hKeq : KS = kZero p E t := hKS.2 hKF.1
      left
      rw [hKeq]
      exact hKF.2.1
    · have hKeq : KS = kZero p E t := hKS.2 hSz.1
      right
      rw [hKeq]
      exact hSz.2.1
  · rcases hall t ht htL with hKF | hSz
    · have hKeq : KS = kZero p E t := hKS.2 hKF.1
      rw [hKeq]
      exact hKF.2.2.2.1
    · have hKeq : KS = kZero p E t := hKS.2 hSz.1
      rw [hKeq]
      exact hSz.2.2

end CFSG.RankThree.PartOne.S13K
