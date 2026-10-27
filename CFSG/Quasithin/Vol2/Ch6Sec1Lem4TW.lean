module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TD
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TC

public noncomputable section

namespace CFSG.Quasithin.H13.Tits614

open CFSG.Sporadic.Schreier.Tits CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.ChainArrays
open scoped commutatorElement

theorem mem_titsS_of_mem_normalizer614
    {d : Equiv.Perm (Fin 1755)} (hd : d ∈ titsD)
    (hn : d ∈ Subgroup.normalizer (titsS : Set (Equiv.Perm (Fin 1755)))) : d ∈ titsS := by
  have hzc : d * titsZ * d⁻¹ ∈
      ((Subgroup.center titsS).map titsS.subtype : Set (Equiv.Perm (Fin 1755))) := by
    have hmem : d * titsZ * d⁻¹ ∈ titsS := (Subgroup.mem_normalizer_iff.mp hn _).mp titsZ_mem_titsS
    refine ⟨⟨_, hmem⟩, Subgroup.mem_center_iff.mpr fun s => Subtype.ext ?_, rfl⟩
    have hs' : d⁻¹ * s * d ∈ titsS := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) s).mp s.2
      simpa using this
    have hzs := Subgroup.mem_centralizer_iff.mp titsZ_mem_centralizer_S _ hs'
    show (s : Equiv.Perm (Fin 1755)) * (d * titsZ * d⁻¹) = d * titsZ * d⁻¹ * s
    calc (s : Equiv.Perm (Fin 1755)) * (d * titsZ * d⁻¹)
        = d * ((d⁻¹ * s * d) * titsZ) * d⁻¹ := by group
      _ = d * (titsZ * (d⁻¹ * s * d)) * d⁻¹ := by rw [hzs]
      _ = d * titsZ * d⁻¹ * s := by group
  rw [titsS_center] at hzc
  have hz : d * titsZ * d⁻¹ = titsZ := by
    rcases hzc with h | h
    · exfalso
      apply titsZ_ne_one
      have := congrArg (fun x => d⁻¹ * x * d) h
      simpa [mul_assoc] using this
    · exact h
  have hdH : d ∈ titsH := by
    rw [← titsD_centralizer_z]
    refine ⟨hd, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc d * titsZ = d * titsZ * d⁻¹ * d := by group
      _ = titsZ * d := by rw [hz]
  exact mem_titsS_of_normalizes614 hdH fun s hs => (Subgroup.mem_normalizer_iff.mp hn s).mp hs

theorem pCoreOf_titsH_le614 :
    CFSG.Open.pCoreOf 2 titsH ≤ titsJ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSH := titsS_le_titsH
  have hS2 : IsPGroup 2 (titsS.subgroupOf titsH) := IsPGroup.of_card (n := 11) (by
    rw [card_subgroupOf_eq hSH, titsQS_facts.2.2.2]; norm_num)
  have hidx : (titsS.subgroupOf titsH).index = 5 := by
    have := (titsS.subgroupOf titsH).card_mul_index
    rw [card_subgroupOf_eq hSH, titsQS_facts.2.2.2, titsQH_facts.2.2.2] at this
    omega
  let P : Sylow 2 titsH := hS2.toSylow (by rw [hidx]; decide)
  have : (CFSG.Open.pCore 2 titsH).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hcore : CFSG.Open.pCore 2 titsH ≤ (P : Subgroup titsH) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup 2).le_sylow_of_normal P
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyS : (y : Equiv.Perm (Fin 1755)) ∈ titsS := hcore hy
  have hpH : pElt ∈ titsH := pElt_mem
  have hyp : (⟨pElt, hpH⟩ : titsH)⁻¹ * y * ⟨pElt, hpH⟩ ∈ CFSG.Open.pCore 2 titsH := by
    have hn := CFSG.LieType.BorelTits.pCore_normal (r := 2) (G := titsH)
    have := hn.conj_mem y hy (⟨pElt, hpH⟩ : titsH)⁻¹
    simpa using this
  have hypS : pElt⁻¹ * y * pElt ∈ titsS := hcore hyp
  exact mem_titsJ_of_conj614 hyS hypS

theorem eq_titsH_of_relIndex_five614
    {P : Subgroup (Equiv.Perm (Fin 1755))} (hPD : P ≤ titsD) (hSP : titsS ≤ P)
    (h5 : titsS.relIndex P = 5) : P = titsH := by
  classical
  set S' := titsS.subgroupOf P with hS'
  have hS'2 : IsPGroup 2 S' := IsPGroup.of_card (n := 11) (by
    rw [card_subgroupOf_eq hSP, titsQS_facts.2.2.2]; norm_num)
  have hcore := commutator_le_normalCore_of_index_five614 hS'2 h5
  set C₀ := S'.normalCore.map P.subtype with hC₀
  have hRC₀ : titsR ≤ C₀ := by
    have hR : titsR = ⁅titsS, titsS⁆ := by
      have h1 : (titsR.subgroupOf titsS).map titsS.subtype = titsR := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr titsR_le_titsS]
      rw [← h1, titsR_eq_commutator, commutator_def, Subgroup.map_commutator,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h2 : S'.map P.subtype = titsS := by
      rw [hS', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSP]
    rw [hR, ← h2, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hcore
  have hfix : ∀ g ∈ P, ((g 0 : Fin 1755) : ℕ) < 3 := by
    intro g hg
    apply fix_titsR614
    intro r hr
    obtain ⟨c, hc, rfl⟩ := hRC₀ hr
    have hc' : (⟨g, hg⟩ : P)⁻¹ * c * ⟨g, hg⟩ ∈ S'.normalCore := by
      have := (Subgroup.normalCore_normal S').conj_mem c hc (⟨g, hg⟩ : P)⁻¹
      simpa using this
    have h0 : (((⟨g, hg⟩ : P)⁻¹ * c * ⟨g, hg⟩ : P) : Equiv.Perm (Fin 1755)) ∈ titsS :=
      Subgroup.normalCore_le S' hc'
    have hfix0 : (g⁻¹ * c * g : Equiv.Perm (Fin 1755)) 0 = 0 :=
      (mem_titsH_iff.mp (titsS_le_titsH h0)).2
    have := congrArg g hfix0
    show (c : Equiv.Perm (Fin 1755)) (g 0) = g 0
    simp only [Equiv.Perm.mul_apply] at this
    rw [← Equiv.Perm.mul_apply g g⁻¹, mul_inv_cancel, Equiv.Perm.one_apply] at this
    exact this
  have horb : (MulAction.orbit P (0 : Fin 1755)).ncard ≤ 3 := by
    have hsub : MulAction.orbit P (0 : Fin 1755) ⊆ {0, 1, 2} := by
      rintro _ ⟨⟨g, hg⟩, rfl⟩
      have h := hfix g hg
      show g 0 ∈ ({0, 1, 2} : Set (Fin 1755))
      have h3 : ((g 0 : Fin 1755) : ℕ) = 0 ∨ ((g 0 : Fin 1755) : ℕ) = 1 ∨
          ((g 0 : Fin 1755) : ℕ) = 2 := by omega
      rcases h3 with h3 | h3 | h3
      · exact Or.inl (Fin.ext h3)
      · exact Or.inr (Or.inl (Fin.ext h3))
      · exact Or.inr (Or.inr (Fin.ext h3))
    calc (MulAction.orbit P (0 : Fin 1755)).ncard ≤ ({0, 1, 2} : Set (Fin 1755)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 3 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          refine (Nat.succ_le_succ (Set.ncard_insert_le _ _)).trans ?_
          rw [Set.ncard_singleton]
  have hstab : S' ≤ MulAction.stabilizer P (0 : Fin 1755) := by
    intro s hs
    rw [MulAction.mem_stabilizer_iff]
    exact (mem_titsH_iff.mp (titsS_le_titsH hs)).2
  have hdvd : (MulAction.stabilizer P (0 : Fin 1755)).index ∣ 5 :=
    h5 ▸ Subgroup.index_dvd_of_le hstab
  have hidx1 : (MulAction.stabilizer P (0 : Fin 1755)).index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
    · exact h
    · rw [MulAction.index_stabilizer] at h
      omega
  rw [Subgroup.index_eq_one] at hidx1
  have hPH : P ≤ titsH := fun g hg => by
    have : (⟨g, hg⟩ : P) ∈ MulAction.stabilizer P (0 : Fin 1755) := hidx1 ▸ Subgroup.mem_top _
    exact mem_titsH_iff.mpr ⟨hPD hg, MulAction.mem_stabilizer_iff.mp this⟩
  apply Subgroup.eq_of_le_of_card_ge hPH
  have hcardP : Nat.card P = 10240 := by
    have := S'.card_mul_index
    rw [card_subgroupOf_eq hSP, titsQS_facts.2.2.2, show S'.index = 5 from h5] at this
    omega
  rw [hcardP, titsQH_facts.2.2.2]

theorem titsGen1_not_mem_titsD614
    : titsGen 1 ∉ titsD := fun h =>
  titsGen1_not_mem (mem_titsS_of_mem_normalizer614 h titsGen1_mem_normalizer)

theorem mem_normalizer_of_closure614 {X : Set (Equiv.Perm (Fin 1755))}
    {g : Equiv.Perm (Fin 1755)} (h : ∀ x ∈ X, g * x * g⁻¹ ∈ Subgroup.closure X) :
    g ∈ Subgroup.normalizer ((Subgroup.closure X : Subgroup _) : Set (Equiv.Perm (Fin 1755))) := by
  apply mem_normalizer_of_conj
  have hle : Subgroup.closure X ≤ (Subgroup.closure X).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact h x hx
  intro r hr
  have := Subgroup.mem_comap.mp (hle hr)
  rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem titsJ_le_of_wc614
    {Tst U : Subgroup (Equiv.Perm (Fin 1755))} (hTA : Tst ≤ titsA) (hT2 : IsPGroup 2 Tst)
    (hST : titsS ≤ Tst) (hUT : U ≤ Tst) (hU1 : U ≠ ⊥)
    (hHU : titsH ≤ Subgroup.normalizer (U : Set (Equiv.Perm (Fin 1755))))
    (hwc : ∀ d ∈ titsD, U.map (MulAut.conj d).toMonoidHom ≤ Tst →
      U.map (MulAut.conj d).toMonoidHom = U) : titsJ ≤ U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTD : Tst ⊓ titsD = titsS := by
    have hle : titsS ≤ Tst ⊓ titsD := le_inf hST titsS_le_titsD
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    obtain ⟨k, hk⟩ := (hT2.to_inf_left (K := titsD)).exists_card_eq
    have hdvd : Nat.card (Tst ⊓ titsD : Subgroup _) ∣ 17971200 :=
      card_titsD ▸ Subgroup.card_dvd_of_le inf_le_right
    rw [hk] at hdvd ⊢
    rw [titsQS_facts.2.2.2]
    have hk11 : k ≤ 11 := by
      by_contra h
      have : 2 ^ 12 ∣ 17971200 := (pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    calc 2 ^ k ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) hk11
      _ = 2048 := by norm_num
  set U₁ := U ⊓ titsD with hU₁
  have hU₁S : U₁ ≤ titsS := hTD ▸ inf_le_inf_right _ hUT
  have hDU₁ : ∀ g ∈ titsA, g ∈ Subgroup.normalizer (U : Set (Equiv.Perm (Fin 1755))) →
      g ∈ Subgroup.normalizer (U₁ : Set (Equiv.Perm (Fin 1755))) := by
    intro g hgA hgU
    rw [Subgroup.mem_normalizer_iff] at hgU ⊢
    intro x
    constructor
    · rintro ⟨hxU, hxD⟩
      exact ⟨(hgU x).mp hxU, titsD_conj_mem hgA hxD⟩
    · rintro ⟨hxU, hxD⟩
      refine ⟨(hgU x).mpr hxU, ?_⟩
      have := titsD_conj_mem (inv_mem hgA) hxD
      simpa [mul_assoc] using this
  have hHU₁ : titsH ≤ Subgroup.normalizer (U₁ : Set (Equiv.Perm (Fin 1755))) := fun h hh =>
    hDU₁ h (titsD_le_titsA (titsH_le_titsD hh)) (hHU hh)
  have hU₁2 : IsPGroup 2 U₁ := (hT2.to_le hUT).to_inf_left
  have hU₁J : U₁ ≤ titsJ := (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hU₁S.trans titsS_le_titsH) hHU₁ hU₁2).trans pCoreOf_titsH_le614
  have hzp : pElt * titsZ = titsZ * pElt :=
    (Subgroup.mem_centralizer_iff.mp titsZ_mem_centralizer_H _ pElt_mem)
  rcases le_or_le_of_five614 titsE614_le_J titsE614_le_commutator titsQJ_facts.2.2.2
      card_titsE614 (fun a ha b hb => titsE614_comm ha hb) pElt_pow_five pElt_mem_normalizer_E
      (hHU₁ pElt_mem) hU₁J (titsJ_le_titsH.trans hHU₁) titsZ_mem_titsE614 titsZ_ne_one hzp
      (fun x hx hxp => eq_of_mem_titsJ_of_commute614 hx hxp) with hE | hJ
  swap
  · exact hJ.trans inf_le_left
  exfalso
  have hU₁K : U₁ ≤ titsK := hE.trans titsE614_le_K
  have hNK : titsN ≤ Subgroup.normalizer (titsK : Set (Equiv.Perm (Fin 1755))) :=
    titsN_le_NK.trans inf_le_right
  have hKT : titsK ≤ Tst := titsK_le_titsS.trans hST
  obtain ⟨Q, hQT, hUQ, hNQ⟩ : ∃ Q : Subgroup (Equiv.Perm (Fin 1755)), Q ≤ Tst ∧ U ≤ Q ∧
      titsN ≤ Subgroup.normalizer (Q : Set (Equiv.Perm (Fin 1755))) := by
    by_cases hUD : U ≤ titsD
    · refine ⟨titsK, hKT, fun x hx => hU₁K ⟨hx, hUD hx⟩, hNK⟩
    · obtain ⟨u, huU, huD⟩ := Set.not_subset.mp hUD
      have huT : u ∈ Tst := hUT huU
      have huA : u ∈ titsA := hTA huT
      have huS : u ∈ Subgroup.normalizer (titsS : Set (Equiv.Perm (Fin 1755))) := by
        apply mem_normalizer_of_conj
        intro s hs
        rw [← hTD]
        exact ⟨Tst.mul_mem (Tst.mul_mem huT (hST hs)) (Tst.inv_mem huT),
          titsD_conj_mem huA (titsS_le_titsD hs)⟩
      have ha₁A : titsGen 1 ∈ titsA := titsGen_mem_titsA (by norm_num)
      have hs₀D : u * (titsGen 1)⁻¹ ∈ titsD := by
        have h2 := Subgroup.mul_mem_iff_of_index_two titsD_index
          (a := (⟨u, huA⟩ : titsA)) (b := (⟨titsGen 1, ha₁A⟩ : titsA)⁻¹)
        have hu' : (⟨u, huA⟩ : titsA) ∉ titsD.subgroupOf titsA := huD
        have ha' : (⟨titsGen 1, ha₁A⟩ : titsA)⁻¹ ∉ titsD.subgroupOf titsA := fun h =>
          titsGen1_not_mem_titsD614 (Subgroup.mem_subgroupOf.mp (by simpa using inv_mem h))
        exact h2.mpr (iff_of_false hu' ha')
      have hs₀S : u * (titsGen 1)⁻¹ ∈ titsS := mem_titsS_of_mem_normalizer614 hs₀D
        (mul_mem huS (inv_mem titsGen1_mem_normalizer))
      set s₀ := u * (titsGen 1)⁻¹ with hs₀
      have hus : u = s₀ * titsGen 1 := by rw [hs₀]; group
      have hcomm : ∀ h ∈ titsH, tcomm u h ∈ titsE614 := by
        intro h hh
        apply hE
        have hhD : h ∈ titsD := titsH_le_titsD hh
        refine ⟨?_, ?_⟩
        · rw [tcomm]
          have h1 : h⁻¹ * u * h ∈ U := by
            have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hHU hh)) u).mp huU
            simpa using this
          have e : u⁻¹ * h⁻¹ * u * h = u⁻¹ * (h⁻¹ * u * h) := by group
          rw [e]
          exact U.mul_mem (U.inv_mem huU) h1
        · rw [tcomm]
          have h1 : u⁻¹ * h⁻¹ * u ∈ titsD := by
            have := titsD_conj_mem (inv_mem huA) (inv_mem hhD)
            simpa using this
          exact titsD.mul_mem h1 hhD
      obtain ⟨hKu, hNu⟩ := outer_facts614 hs₀S (fun i hi => by
        rw [← hus]; exact hcomm _ (hGen_mem hi))
      rw [← hus] at hKu hNu
      have huK : u ∈ Subgroup.normalizer (titsK : Set (Equiv.Perm (Fin 1755))) := by
        rw [titsK_eq_closure614]
        apply mem_normalizer_of_closure614
        rintro _ ⟨j, rfl⟩
        rw [← titsK_eq_closure614]
        exact hKu j j.2
      set Q := Subgroup.closure ((titsK : Set (Equiv.Perm (Fin 1755))) ∪ {u}) with hQ
      have hKQ : titsK ≤ Q := fun k hk => Subgroup.subset_closure (Or.inl hk)
      have huQ : u ∈ Q := Subgroup.subset_closure (Or.inr rfl)
      refine ⟨Q, ?_, ?_, ?_⟩
      · rw [hQ, Subgroup.closure_le]
        rintro x (hx | rfl)
        · exact hKT hx
        · exact huT
      · intro x hx
        by_cases hxD : x ∈ titsD
        · exact hKQ (hU₁K ⟨hx, hxD⟩)
        · have hxu : x * u⁻¹ ∈ titsD := by
            have hxA : x ∈ titsA := hTA (hUT hx)
            have h2 := Subgroup.mul_mem_iff_of_index_two titsD_index
              (a := (⟨x, hxA⟩ : titsA)) (b := (⟨u, huA⟩ : titsA)⁻¹)
            have hx' : (⟨x, hxA⟩ : titsA) ∉ titsD.subgroupOf titsA := hxD
            have hu' : (⟨u, huA⟩ : titsA)⁻¹ ∉ titsD.subgroupOf titsA := fun h =>
              huD (Subgroup.mem_subgroupOf.mp (by simpa using inv_mem h))
            exact h2.mpr (iff_of_false hx' hu')
          have hxuK : x * u⁻¹ ∈ titsK := hU₁K ⟨U.mul_mem hx (U.inv_mem huU), hxu⟩
          have e : x = x * u⁻¹ * u := by group
          rw [e]
          exact Q.mul_mem (hKQ hxuK) huQ
      · rw [titsN_eq_closure614, Subgroup.closure_le]
        rintro _ ⟨j, rfl⟩
        have hnN : nGen j ∈ titsN := nGen_mem j.2
        have hnK := hNK hnN
        have hinv : (nGen j)⁻¹ ∈ Subgroup.normalizer (Q : Set (Equiv.Perm (Fin 1755))) := by
          rw [hQ]
          apply mem_normalizer_of_closure614
          rintro x (hx | hx)
          · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hnK) x).mp hx
            exact Subgroup.subset_closure (Or.inl this)
          · rw [Set.mem_singleton_iff.mp hx]
            have hk := hNu j j.2
            rw [tcomm] at hk
            have e : (nGen j)⁻¹ * u * (nGen j)⁻¹⁻¹ = u * (u⁻¹ * (nGen j)⁻¹ * u * nGen j) := by
              group
            rw [e]
            exact Q.mul_mem huQ (hKQ hk)
        have := inv_mem hinv
        rwa [inv_inv] at this
  have hNU : titsN ≤ Subgroup.normalizer (U : Set (Equiv.Perm (Fin 1755))) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : U.map (MulAut.conj n).toMonoidHom ≤ Tst := by
      refine (Subgroup.map_mono hUQ).trans ?_
      have hQn : Q.map (MulAut.conj n).toMonoidHom = Q :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNQ hn)
      rw [hQn]
      exact hQT
    exact hwc n (titsN_le_titsD hn) hle
  have hDU : titsD ≤ Subgroup.normalizer (U : Set (Equiv.Perm (Fin 1755))) := by
    rw [← titsH_sup_N]
    exact sup_le hHU hNU
  have hDU₁ : titsD ≤ Subgroup.normalizer (U₁ : Set (Equiv.Perm (Fin 1755))) := fun d hd =>
    hDU₁ d (titsD_le_titsA hd) (hDU hd)
  have hU₁bot : U₁ = ⊥ := by
    have : IsSimpleGroup titsD := titsD_simple
    have hn : (U₁.subgroupOf titsD).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hDU₁
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (U₁.subgroupOf titsD) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      exact h.eq_bot_of_le inf_le_right
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h
      have := Subgroup.card_le_of_le (h.trans hU₁S)
      rw [card_titsD, titsQS_facts.2.2.2] at this
      norm_num at this
  apply hU1
  rw [eq_bot_iff]
  intro u hu
  have huA : u ∈ titsA := hTA (hUT hu)
  have hcen : ∀ d ∈ titsD, u * d * u⁻¹ = d := by
    intro d hd
    have h1 : u * d * u⁻¹ * d⁻¹ ∈ U₁ := by
      refine ⟨?_, ?_⟩
      · have : d * u⁻¹ * d⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hDU hd) _).mp (U.inv_mem hu)
        have e : u * d * u⁻¹ * d⁻¹ = u * (d * u⁻¹ * d⁻¹) := by group
        rw [e]
        exact U.mul_mem hu this
      · exact titsD.mul_mem (titsD_conj_mem huA hd) (titsD.inv_mem hd)
    rw [hU₁bot, Subgroup.mem_bot] at h1
    calc u * d * u⁻¹ = u * d * u⁻¹ * d⁻¹ * d := by group
      _ = d := by rw [h1, one_mul]
  have h1 : titsConj ⟨u, huA⟩ = 1 := by
    refine MulEquiv.ext fun d => Subtype.ext ?_
    rw [coe_titsConj_apply, MulAut.one_apply]
    exact hcen d d.2
  have := titsConj_injective (h1.trans (map_one titsConj).symm)
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

end CFSG.Quasithin.H13.Tits614
