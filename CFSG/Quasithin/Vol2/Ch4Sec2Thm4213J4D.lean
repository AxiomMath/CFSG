module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4C

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace NoJ4

variable {G : Type} [Group G] [Finite G]

theorem conjClosure_LH {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K) :
    conjClosure (perfectCore (L ⊓ H)) (H ⊓ M) = perfectCore (L ⊓ H) := by
  refine le_antisymm (conjClosure_le fun h hh z hz => ?_) (le_conjClosure _ _)
  exact (Subgroup.mem_normalizer_iff.mp (c.LH_normal hh) z).mp hz

theorem v_eq (hBlk : J4BlockFacts) {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) :
    ⁅reducedAggregate (L ⊔ T), L⁆ = pCoreOf 2 (perfectCore (L ⊓ H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLH
  set V := ⁅reducedAggregate (L ⊔ T), L⁆ with hV
  have h := c.hypC28
  have hM0 := conjClosure_LH c
  have hVL : V ≤ LH := by
    have := h.V_le
    rwa [hM0] at this
  have hcomm : ⁅V, LH⁆ = V := by
    have := h.V_comm
    rwa [hM0] at this
  have hLHn : LH ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr (by
      rw [Subgroup.commutator_comm, hcomm])
  have hV2 : IsPGroup 2 ↥V := fun g =>
    ⟨1, Subtype.ext (by simpa [pow_one] using h.V_elem.2 g g.2)⟩
  have hVE : V ≤ pCoreOf 2 LH := le_pCoreOf_of_le_normalizer 2 hVL hLHn hV2
  have hEn : LH ≤ Subgroup.normalizer (V : Set G) := hLHn
  rcases (blockFacts_of_case6 hBlk c h6).2.2.1 V hVE hEn with hb | he
  · exact absurd hb h.V_ne
  · exact he

theorem pCoreOf_LH_le {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K) :
    pCoreOf 2 (perfectCore (L ⊓ H)) ≤ pCoreOf 2 I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLH
  set E := pCoreOf 2 LH with hE
  have hsyl := c.hypC28.sylow
  rw [conjClosure_LH c] at hsyl
  have hLHM : LH ≤ H ⊓ M := (perfectCore_le (L ⊓ H)).trans
    (le_inf inf_le_right (inf_le_left.trans c.hyp421.L_le))
  have hEC : E ≤ centralizerSection (H ⊓ M) LH E := by
    intro e he
    have heLH : e ∈ LH := pCoreOf_le 2 LH he
    refine ⟨hLHM heLH, Subgroup.le_normalizer heLH, le_normalizer_pCoreOf 2 LH heLH, ?_⟩
    intro x hx
    have h1 : x * e * x⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 LH hx) e).mp he
    exact E.mul_mem h1 (E.inv_mem he)
  have hEn : centralizerSection (H ⊓ M) LH E ≤ Subgroup.normalizer (E : Set G) :=
    fun m hm => hm.2.2.1
  have h1 : E ≤ pCoreOf 2 (centralizerSection (H ⊓ M) LH E) :=
    le_pCoreOf_of_le_normalizer 2 hEC hEn (pCoreOf_isPGroup 2 LH)
  exact h1.trans (CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsyl)

theorem LH_le {T M L Mm I H K : Subgroup G} (hy : Hyp4_2_3 G T M L Mm I) (hIH : InM I H)
    (c : Conf4212 G T M L I H K) : perfectCore (L ⊓ H) ≤ I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLH
  set E := pCoreOf 2 LH with hE
  have hLHL : LH ≤ L := (perfectCore_le (L ⊓ H)).trans inf_le_left
  have hLHH : LH ≤ H := (perfectCore_le (L ⊓ H)).trans inf_le_right
  have hLM : L ≤ M := c.hyp421.L_le
  have hsyl := c.hypC28.sylow
  rw [conjClosure_LH c] at hsyl
  set C₀ := centralizerSection (H ⊓ M) LH E with hC₀
  have hOC : pCoreOf 2 L ⊓ C₀ ≤ pCoreOf 2 I := by
    have hn : C₀ ≤ Subgroup.normalizer ((pCoreOf 2 L ⊓ C₀ : Subgroup G) : Set G) := by
      intro m hm
      have hmL : m ∈ Subgroup.normalizer (L : Set G) := c.normal hm.1.2
      have hmO : m ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
        normalizer_le_normalizer_pCoreOf 2 L hmL
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hyO, hyC⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hmO y).mp hyO,
          C₀.mul_mem (C₀.mul_mem hm hyC) (C₀.inv_mem hm)⟩
      · rintro ⟨hyO, hyC⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp hmO y).mpr hyO, ?_⟩
        have := C₀.mul_mem (C₀.mul_mem (C₀.inv_mem hm) hyC) hm
        simpa [mul_assoc] using this
    have h1 : pCoreOf 2 L ⊓ C₀ ≤ pCoreOf 2 C₀ :=
      le_pCoreOf_of_le_normalizer 2 inf_le_right hn
        ((pCoreOf_isPGroup 2 L).to_le inf_le_left)
    exact h1.trans (CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsyl)
  have hMp : conjClosure L T = L := c.conjClosure_eq
  have hLI : L ≤ I ⊔ pCoreOf 2 L := by
    have := hy.gammaStar.1.1.2.2.1
    rwa [hMp] at this
  have hIn : I ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (c.I_le.trans c.normal).trans (normalizer_le_normalizer_pCoreOf 2 L)
  intro l hl
  obtain ⟨i, hi, o, ho, hio⟩ := (mem_sup_of_le_normalizer hIn).mp (hLI (hLHL hl))
  have hoe : o = i⁻¹ * l := by rw [← hio]; group
  have hoH : o ∈ H := by
    rw [hoe]
    exact H.mul_mem (H.inv_mem (hIH.2 hi)) (hLHH hl)
  have hoL : o ∈ L := pCoreOf_le 2 L ho
  have hoLH : o ∈ Subgroup.normalizer (LH : Set G) :=
    normalizer_le_normalizer_perfectCore (L ⊓ H) (Subgroup.le_normalizer ⟨hoL, hoH⟩)
  have hoE : o ∈ Subgroup.normalizer (E : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 LH hoLH
  have hoC : o ∈ C₀ := by
    refine ⟨⟨hoH, hLM hoL⟩, hoLH, hoE, fun x hx => ?_⟩
    have h1 : x * o * x⁻¹ * o⁻¹ ∈ LH := by
      have := (Subgroup.mem_normalizer_iff.mp hoLH x⁻¹).mp (LH.inv_mem hx)
      have e : x * o * x⁻¹ * o⁻¹ = x * (o * x⁻¹ * o⁻¹) := by group
      rw [e]
      exact LH.mul_mem hx this
    have h2 : x * o * x⁻¹ * o⁻¹ ∈ pCoreOf 2 L := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L (hLHL hx)) o).mp ho
      exact (pCoreOf 2 L).mul_mem this ((pCoreOf 2 L).inv_mem ho)
    have hn : LH ≤ Subgroup.normalizer ((LH ⊓ pCoreOf 2 L : Subgroup G) : Set G) := by
      intro y hy'
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have hyO := le_normalizer_pCoreOf 2 L (hLHL hy')
      constructor
      · rintro ⟨hzL, hzO⟩
        exact ⟨LH.mul_mem (LH.mul_mem hy' hzL) (LH.inv_mem hy'),
          (Subgroup.mem_normalizer_iff.mp hyO z).mp hzO⟩
      · rintro ⟨hzL, hzO⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hyO z).mpr hzO⟩
        have := LH.mul_mem (LH.mul_mem (LH.inv_mem hy') hzL) hy'
        simpa [mul_assoc] using this
    have h3 : LH ⊓ pCoreOf 2 L ≤ E :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left hn ((pCoreOf_isPGroup 2 L).to_le inf_le_right)
    exact h3 ⟨h1, h2⟩
  have hoR : o ∈ pCoreOf 2 I := hOC ⟨ho, hoC⟩
  rw [← hio]
  exact I.mul_mem hi (pCoreOf_le 2 I hoR)

theorem mem_LH_of (hBlk : J4BlockFacts) {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) {i k : G} (hiN : i ∈ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G)) (hk : k ∈ K)
    (hkc : k⁻¹ * i ∈ Subgroup.centralizer (K : Set G)) : k ∈ perfectCore (L ⊓ H) := by
  set LH := perfectCore (L ⊓ H) with hLH
  set cc := k⁻¹ * i with hcc
  have hccK : ∀ y ∈ K, y * cc = cc * y := fun y hy' => Subgroup.mem_centralizer_iff.mp hkc y hy'
  have hccN : cc ∈ Subgroup.normalizer (LH : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy'
      rw [← hccK y (c.LH_le hy'), mul_inv_cancel_right]
      exact hy'
    · intro hy'
      have hz := hccK (cc * y * cc⁻¹) (c.LH_le hy')
      have e : y = cc * y * cc⁻¹ := by
        calc y = cc⁻¹ * (cc * y * cc⁻¹) * cc := by group
          _ = cc⁻¹ * (cc * (cc * y * cc⁻¹)) := by rw [mul_assoc, hz]
          _ = cc * y * cc⁻¹ := by group
      rw [e]
      exact hy'
  have hkN : k ∈ Subgroup.normalizer (LH : Set G) := by
    have : k = i * cc⁻¹ := by rw [hcc]; group
    rw [this]
    exact Subgroup.mul_mem _ hiN (Subgroup.inv_mem _ hccN)
  have h1 : K ⊓ Subgroup.normalizer (LH : Set G) = LH := (blockFacts_of_case6 hBlk c h6).1
  rw [← h1]
  exact ⟨hk, hkN⟩

theorem R_eq
    (hOut : J4OutTrivial) (hBlk : J4BlockFacts) {T M L Mm I H K : Subgroup G}
    (hy : Hyp4_2_3 G T M L Mm I) (hIH : InM I H) (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) :
    pCoreOf 2 I = pCoreOf 2 (perfectCore (L ⊓ H)) ⊔
        (pCoreOf 2 I ⊓ Subgroup.centralizer (K : Set G)) ∧
      pCoreOf 2 (perfectCore (L ⊓ H)) ⊓ (pCoreOf 2 I ⊓ Subgroup.centralizer (K : Set G)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLH
  set E := pCoreOf 2 LH with hE
  set R := pCoreOf 2 I with hR
  have hK := h6.1
  have hEK : E ≤ K := (pCoreOf_le 2 LH).trans c.LH_le
  have hER : E ≤ R := pCoreOf_LH_le c
  have hLHI : LH ≤ I := LH_le hy hIH c
  have hKC := inf_centralizer_eq_bot hK
  refine ⟨le_antisymm (fun ρ hρ => ?_) (sup_le hER inf_le_left), ?_⟩
  · have hρI : ρ ∈ I := pCoreOf_le 2 I hρ
    have hρH : ρ ∈ H := hIH.2 hρI
    obtain ⟨k, hk, hkc⟩ := exists_mem_centralizer hOut hK (normal hy hIH c hK hρH)
    have hρN : ρ ∈ Subgroup.normalizer (LH : Set G) := c.LH_normal ⟨hρH, c.I_le hρI⟩
    have hkLH : k ∈ LH := mem_LH_of hBlk c h6 hρN hk hkc
    set cc := k⁻¹ * ρ with hcc
    have hccK : ∀ y ∈ K, y * cc = cc * y := fun y hy' =>
      Subgroup.mem_centralizer_iff.mp hkc y hy'
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 I) ⟨ρ, hρ⟩
    have hρn : ρ ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hkcomm : Commute k cc := (hccK k hk)
    have hρe : ρ = k * cc := by rw [hcc]; group
    have hkn : k ^ 2 ^ n = 1 := by
      have h1 : k ^ 2 ^ n * cc ^ 2 ^ n = 1 := by
        rw [← hkcomm.mul_pow, ← hρe, hρn]
      have h2 : k ^ 2 ^ n = (cc ^ 2 ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : k ^ 2 ^ n ∈ K ⊓ Subgroup.centralizer (K : Set G) := by
        refine ⟨K.pow_mem hk _, ?_⟩
        rw [h2]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hkc _)
      rw [hKC] at h3
      exact Subgroup.mem_bot.mp h3
    have hRLH : R ⊓ LH ≤ E := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        ((pCoreOf_isPGroup 2 I).to_le inf_le_left)
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have hlR := le_normalizer_pCoreOf 2 I (hLHI hl)
      constructor
      · rintro ⟨hzR, hzL⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hlR z).mp hzR,
          LH.mul_mem (LH.mul_mem hl hzL) (LH.inv_mem hl)⟩
      · rintro ⟨hzR, hzL⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp hlR z).mpr hzR, ?_⟩
        have := LH.mul_mem (LH.mul_mem (LH.inv_mem hl) hzL) hl
        simpa [mul_assoc] using this
    have hkl : ∀ l ∈ LH, k * l * k⁻¹ * l⁻¹ ∈ E := by
      intro l hl
      have hcl : cc * l * cc⁻¹ = l := by
        rw [← hccK l (c.LH_le hl), mul_inv_cancel_right]
      have e : k * l * k⁻¹ * l⁻¹ = ρ * l * ρ⁻¹ * l⁻¹ := by
        rw [hρe]
        calc k * l * k⁻¹ * l⁻¹ = k * (cc * l * cc⁻¹) * k⁻¹ * l⁻¹ := by rw [hcl]
          _ = k * cc * l * (k * cc)⁻¹ * l⁻¹ := by group
      apply hRLH
      refine ⟨?_, LH.mul_mem (LH.mul_mem (LH.mul_mem hkLH hl) (LH.inv_mem hkLH)) (LH.inv_mem hl)⟩
      rw [e]
      have h1 : ρ * l * ρ⁻¹ ∈ I := I.mul_mem (I.mul_mem hρI (hLHI hl)) (I.inv_mem hρI)
      have h2 : l * ρ⁻¹ * l⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 I (hLHI hl)) _).mp (R.inv_mem hρ)
      have e2 : ρ * l * ρ⁻¹ * l⁻¹ = ρ * (l * ρ⁻¹ * l⁻¹) := by group
      rw [e2]
      exact R.mul_mem hρ h2
    have hkE : k ∈ E := by
      have hn' : Subgroup.zpowers k ≤ Subgroup.normalizer (E : Set G) :=
        Subgroup.zpowers_le.mpr (le_normalizer_pCoreOf 2 LH hkLH)
      have hpk : IsPGroup 2 ↥(Subgroup.zpowers k) := by
        rintro ⟨y, hy⟩
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        refine ⟨n, Subtype.ext ?_⟩
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hkn, one_zpow]
      have hp : IsPGroup 2 ↥(Subgroup.zpowers k ⊔ E) :=
        IsPGroup.to_sup_of_normal_right' hpk (pCoreOf_isPGroup 2 LH) hn'
      have hle : Subgroup.zpowers k ⊔ E ≤ LH :=
        sup_le (Subgroup.zpowers_le.mpr hkLH) (pCoreOf_le 2 LH)
      have hnorm : LH ≤ Subgroup.normalizer ((Subgroup.zpowers k ⊔ E : Subgroup G) : Set G) := by
        intro l hl
        refine Subgroup.mem_normalizer_fintype fun z hz => ?_
        have hEn := le_normalizer_pCoreOf 2 LH hl
        have hsub : (Subgroup.zpowers k ⊔ E).map (MulAut.conj l).toMonoidHom ≤
            Subgroup.zpowers k ⊔ E := by
          rw [Subgroup.map_sup]
          refine sup_le ?_ ?_
          · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
            have h1 := hkl l hl
            have e : (MulAut.conj l).toMonoidHom k = (k * l * k⁻¹ * l⁻¹)⁻¹ * k := by
              simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
              group
            rw [e]
            exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (E.inv_mem h1))
              (Subgroup.mem_sup_left (Subgroup.mem_zpowers k))
          · rintro _ ⟨e, he, rfl⟩
            exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hEn e).mp he)
        exact hsub ⟨z, hz, rfl⟩
      exact le_pCoreOf_of_le_normalizer 2 hle hnorm hp
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers k))
    have hccR : cc ∈ R := by
      rw [hcc]
      exact R.mul_mem (R.inv_mem (hER hkE)) hρ
    rw [hρe]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hkE) (Subgroup.mem_sup_right ⟨hccR, hkc⟩)
  · refine eq_bot_iff.mpr fun x hx => ?_
    have h1 : x ∈ K ⊓ Subgroup.centralizer (K : Set G) := ⟨hEK hx.1, hx.2.2⟩
    rwa [hKC] at h1

end NoJ4

end CFSG.Quasithin.H13.Ch4
