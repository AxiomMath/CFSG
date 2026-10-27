module

public import CFSG.Quasithin.EmptyFaithful.T1515C7Set

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

namespace Seven7Data

variable {V M T : Subgroup G} {hVe : IsElemAbelian 2 V} (d : Seven7Data V M T hVe)
include d

theorem pCore_eq_oTwoUpper [Finite G] :
    pCoreOf 3 (autOn M V) = oTwoUpper (autOn M V) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite ↥V := inferInstance
  apply le_antisymm
  · intro x hx
    have hxA : x ∈ autOn M V := CFSG.LieType.BorelTits.pCoreOf_le 3 _ hx
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 (autOn M V)) ⟨x, hx⟩
    have hk' : x ^ 3 ^ k = 1 := congrArg Subtype.val hk
    refine mem_oTwoUpper_of_odd hxA ?_
    have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
    exact Odd.of_dvd_nat (Odd.pow (by decide)) h1
  · have hP : IsPGroup 3 (oTwoUpper (autOn M V)) :=
      IsPGroup.of_card (n := 3) (by rw [d.ctx.card_P]; norm_num)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 3 (oTwoUpper_le _)
      (le_normalizer_oTwoUpper _) hP


theorem Z₁_eq_inf_centralizer [Finite G] :
    d.Z₁ = V ⊓ Subgroup.centralizer (preOn M V (Subgroup.zpowers d.y) : Set G) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hyfix : d.y ∈ fixingV (fixOf d.y : Set V) := fun s hs => hs
  have hyA : d.y ∈ autOn M V := oTwoUpper_le _ d.gen.yP
  apply le_antisymm
  · intro v hv
    refine Subgroup.mem_inf.mpr ⟨d.Z₁_le_V hv, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hle : preOn M V (Subgroup.zpowers d.y) ≤ preOn M V (fixingV (fixOf d.y : Set V)) := by
      intro x hx
      obtain ⟨hxM, hxN, hxy⟩ := mem_preOn.mp hx
      exact mem_preOn.mpr ⟨hxM, hxN, (Subgroup.zpowers_le.mpr hyfix) hxy⟩
    have hm' := hle hm
    have hm'' : m ∈ M ⊓ Subgroup.centralizer ((d.Z₁'.map V.subtype : Subgroup G) : Set G) := by
      rw [inf_centralizer_eq_preOn d.hMN d.Z₁']
      exact hm'
    exact (Subgroup.mem_centralizer_iff.mp hm''.2 v hv).symm
  · intro v hv
    obtain ⟨hvV, hvc⟩ := Subgroup.mem_inf.mp hv
    obtain ⟨m, hmN, hmM, hmy⟩ := mem_autOn_iff_exists.mp hyA
    have hm : m ∈ preOn M V (Subgroup.zpowers d.y) :=
      mem_preOn.mpr ⟨hmM, hmN, by rw [hmy]; exact Subgroup.mem_zpowers _⟩
    have hcomm : m * v = v * m := Subgroup.mem_centralizer_iff.mp hvc m hm
    refine ⟨⟨v, hvV⟩, ?_, rfl⟩
    show d.y ⟨v, hvV⟩ = ⟨v, hvV⟩
    rw [← hmy]
    refine Subtype.ext ?_
    rw [conj_coe_apply]
    calc m * v * m⁻¹ = v * m * m⁻¹ := by rw [hcomm]
      _ = v := by group

theorem Z₂_eq_inf_centralizer [Finite G] :
    d.Z₂ = V ⊓ Subgroup.centralizer (preOn M V (Subgroup.zpowers d.x) : Set G) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hxfix : d.x ∈ fixingV (fixOf d.x : Set V) := fun s hs => hs
  have hxA : d.x ∈ autOn M V := oTwoUpper_le _ d.gen.xP
  apply le_antisymm
  · intro v hv
    refine Subgroup.mem_inf.mpr ⟨d.Z₂_le_V hv, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hle : preOn M V (Subgroup.zpowers d.x) ≤ preOn M V (fixingV (fixOf d.x : Set V)) := by
      intro x hx
      obtain ⟨hxM, hxN, hxy⟩ := mem_preOn.mp hx
      exact mem_preOn.mpr ⟨hxM, hxN, (Subgroup.zpowers_le.mpr hxfix) hxy⟩
    have hm' := hle hm
    have hm'' : m ∈ M ⊓ Subgroup.centralizer ((d.Z₂'.map V.subtype : Subgroup G) : Set G) := by
      rw [inf_centralizer_eq_preOn d.hMN d.Z₂']
      exact hm'
    exact (Subgroup.mem_centralizer_iff.mp hm''.2 v hv).symm
  · intro v hv
    obtain ⟨hvV, hvc⟩ := Subgroup.mem_inf.mp hv
    obtain ⟨m, hmN, hmM, hmx⟩ := mem_autOn_iff_exists.mp hxA
    have hm : m ∈ preOn M V (Subgroup.zpowers d.x) :=
      mem_preOn.mpr ⟨hmM, hmN, by rw [hmx]; exact Subgroup.mem_zpowers _⟩
    have hcomm : m * v = v * m := Subgroup.mem_centralizer_iff.mp hvc m hm
    refine ⟨⟨v, hvV⟩, ?_, rfl⟩
    show d.x ⟨v, hvV⟩ = ⟨v, hvV⟩
    rw [← hmx]
    refine Subtype.ext ?_
    rw [conj_coe_apply]
    calc m * v * m⁻¹ = v * m * m⁻¹ := by rw [hcomm]
      _ = v := by group


theorem mul_inv_zpow_apply_mem_ker [Finite G] (w : V) (k : ℤ) :
    w * ((d.y ^ k) w)⁻¹ ∈ d.V₂' := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hy3 := SevenGen.y3 d.ctx d.gen
  have hord := d.hyord
  have hsq := d.ctx.sq
  have hcube : ∀ u : V, d.y (d.y (d.y u)) = u := fun u => apply_cube_c4 hy3 u
  have hu1 : ∀ w : V, w * (d.y w)⁻¹ ∈ d.V₂' := by
    intro w
    show normOf d.y (w * (d.y w)⁻¹) = 1
    rw [normOf_apply]
    simp only [map_mul, map_inv, hcube]
    group
  have hmod : d.y ^ k = d.y ^ (k % 3) := by
    have := zpow_mod_orderOf d.y k
    rw [hord] at this
    simpa using this.symm
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [hmod]
  rcases hk with hk | hk | hk
  · rw [hk]
    simp
  · rw [hk]
    simpa using hu1 w
  · rw [hk]
    have h2 : (d.y ^ (2 : ℤ)) w = d.y (d.y w) := by
      rw [zpow_two]
      rfl
    rw [h2]
    have : w * (d.y (d.y w))⁻¹ = (w * (d.y w)⁻¹) * (d.y (w * (d.y w)⁻¹)) := by
      simp only [map_mul, map_inv]
      group
    rw [this]
    refine (d.V₂').mul_mem (hu1 w) ?_
    exact d.hY_zpowers_V₂' (Subgroup.mem_zpowers _) (hu1 w)

theorem V₂_eq_commutator [Finite G] :
    d.V₂ = ⁅V, preOn M V (Subgroup.zpowers d.y)⁆ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hyA : d.y ∈ autOn M V := oTwoUpper_le _ d.gen.yP
  set X : Subgroup G := preOn M V (Subgroup.zpowers d.y) with hX
  have hXM : X ≤ M := inf_le_left
  have hXaut : autOn X V = Subgroup.zpowers d.y := by
    rw [hX, autOn_preOn_inf]
    exact inf_eq_left.mpr (Subgroup.zpowers_le.mpr hyA)
  apply le_antisymm
  ·
    have h1 : ⁅d.V₂, X⁆ = d.V₂ := by
      refine d.commutator_map_eq hXM (W := d.V₂') (c := d.y) ?_ ?_ hXaut ?_
      · exact fun w hw => d.hY_zpowers_V₂' (Subgroup.mem_zpowers _) hw
      · exact fun w hw hgw => d.y_fpf_V₂' hw hgw
      · intro a ha w hw
        rw [hXaut] at ha
        exact d.hY_zpowers_V₂' ha hw
    calc d.V₂ = ⁅d.V₂, X⁆ := h1.symm
      _ ≤ ⁅V, X⁆ := Subgroup.commutator_mono d.V₂_le_V le_rfl
  · rw [Subgroup.commutator_le]
    intro v hv x hx
    obtain ⟨hxM, hxN, hxy⟩ := mem_preOn.mp hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxy
    have hmem := d.mul_inv_zpow_apply_mem_ker ⟨v, hv⟩ k
    have hconj : ((conjAct V ⟨x, hxN⟩ ⟨v, hv⟩ : V) : G) = x * v * x⁻¹ := conj_coe_apply V ⟨x, hxN⟩ ⟨v, hv⟩
    rw [← hk] at hconj
    have : ⁅v, x⁆ = (⟨v, hv⟩ * ((d.y ^ k) ⟨v, hv⟩)⁻¹ : V) := by
      have h2 : (((d.y ^ k) ⟨v, hv⟩ : V) : G) = x * v * x⁻¹ := hconj
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, h2]
      rw [commutatorElement_def]
      group
    rw [this]
    exact ⟨_, hmem, rfl⟩


theorem centerOf_P_eq [Finite G] :
    centerOf (oTwoUpper (autOn M V)) = Subgroup.zpowers d.z := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  rw [← SevenGen.Z_eq_zpowers d.ctx d.gen]
  ext c
  rw [d.ctx.mem_Z_iff]
  simp only [centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]

theorem center_mul_zpowers_mul [Finite G] :
    (centerOf (oTwoUpper (autOn M V)) : Set (MulAut ↥V)) *
        (Subgroup.zpowers d.y : Set (MulAut ↥V)) * (Subgroup.zpowers d.x : Set (MulAut ↥V)) =
      (oTwoUpper (autOn M V) : Set (MulAut ↥V)) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [d.centerOf_P_eq]
  have hy3 := SevenGen.y3 d.ctx d.gen
  have hx3 := SevenGen.x3 d.ctx d.gen
  have hz3 := SevenGen.z3 d.ctx d.gen
  have hyz : d.y * d.z = d.z * d.y := SevenGen.yz d.ctx d.gen
  have hxz : d.x * d.z = d.z * d.x := SevenGen.xz d.ctx d.gen
  have hxy : d.x * d.y * d.x⁻¹ = d.y * d.z ^ 1 := SevenGen.xy_rel d.ctx d.gen
  have hz1 : d.z ≠ 1 := d.gen.z1
  have hy1 : d.y ≠ 1 := SevenGen.y_ne_one d.gen
  have hx1 : d.x ≠ 1 := fun hx => hz1 (by rw [d.gen.zdef, hx]; group)
  set P : Subgroup (MulAut ↥V) := oTwoUpper (autOn M V) with hP
  set Pz : Subgroup (MulAut ↥V) := Subgroup.zpowers d.z with hPz
  set P₁ : Subgroup (MulAut ↥V) := Subgroup.zpowers d.y with hP₁
  set P₂ : Subgroup (MulAut ↥V) := Subgroup.zpowers d.x with hP₂
  have hcP : Nat.card P = 27 := d.ctx.card_P
  have hcz : Nat.card Pz = 3 := by
    rw [hPz, ← SevenGen.Z_eq_zpowers d.ctx d.gen]; exact d.ctx.card_Z
  have hc1 : Nat.card P₁ = 3 := card_pow_gen hy3 hy1
  have hc2 : Nat.card P₂ = 3 := card_pow_gen hx3 hx1
  have hzP : d.z ∈ P := d.ctx.Z_le_P d.gen.zZ
  have hyP : d.y ∈ P := d.gen.yP
  have hxP : d.x ∈ P := d.gen.xP
  have hPzP : Pz ≤ P := Subgroup.zpowers_le.mpr hzP
  have hP₁P : P₁ ≤ P := Subgroup.zpowers_le.mpr hyP
  have hP₂P : P₂ ≤ P := Subgroup.zpowers_le.mpr hxP
  have hinf : Pz ⊓ P₁ = ⊥ := by
    have hdvd : Nat.card ↥(Pz ⊓ P₁) ∣ 3 := hc1 ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hI : Pz ⊓ P₁ = P₁ := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hc1])
      have hyPz : d.y ∈ Pz := by
        have : d.y ∈ Pz ⊓ P₁ := by rw [hI]; exact Subgroup.mem_zpowers _
        exact this.1
      exact SevenGen.y_not_Z d.ctx d.gen (by rw [SevenGen.Z_eq_zpowers d.ctx d.gen]; exact hyPz)
  have hcomm : ∀ a ∈ Pz, ∀ b ∈ P₁, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (((Commute.zpow_zpow (show Commute d.z d.y from hyz.symm) m n)).eq)
  obtain ⟨hcardN, hsetN⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Pz P₁ hcomm
  rw [hinf, Subgroup.card_bot, hcz, hc1] at hcardN
  have hcN : Nat.card ↥(Pz ⊔ P₁) = 9 := by omega
  have hNy : Pz ⊔ P₁ ≤ Subgroup.centralizer ({d.y} : Set (MulAut ↥V)) := by
    refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.mpr ?_
      exact Subgroup.mem_centralizer_singleton_iff.mpr hyz.symm
    · refine Subgroup.zpowers_le.mpr ?_
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hxN : d.x ∉ Pz ⊔ P₁ := by
    intro hx
    have h1 : d.x * d.y = d.y * d.x := Subgroup.mem_centralizer_singleton_iff.mp (hNy hx)
    apply hz1
    have h2 : d.x * d.y * d.x⁻¹ = d.y := by
      rw [h1]; group
    rw [h2, pow_one] at hxy
    have := congrArg (fun q => d.y⁻¹ * q) hxy
    simpa using this.symm
  have hfwd : ∀ h ∈ Pz ⊔ P₁, d.x * h * d.x⁻¹ ∈ Pz ⊔ P₁ := by
    intro h hh
    have hmap : (Pz ⊔ P₁).map (MulAut.conj d.x).toMonoidHom ≤ Pz ⊔ P₁ := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [hPz, MonoidHom.map_zpowers]
        refine Subgroup.zpowers_le.mpr ?_
        have : (MulAut.conj d.x).toMonoidHom d.z = d.z := by
          show d.x * d.z * d.x⁻¹ = d.z
          rw [hxz]; group
        rw [this]
        exact le_sup_left (a := Pz) (b := P₁) (Subgroup.mem_zpowers _)
      · rw [hP₁, MonoidHom.map_zpowers]
        refine Subgroup.zpowers_le.mpr ?_
        have : (MulAut.conj d.x).toMonoidHom d.y = d.y * d.z := by
          show d.x * d.y * d.x⁻¹ = d.y * d.z
          simpa using hxy
        rw [this]
        exact (Pz ⊔ P₁).mul_mem (le_sup_right (a := Pz) (b := P₁) (Subgroup.mem_zpowers _))
          (le_sup_left (a := Pz) (b := P₁) (Subgroup.mem_zpowers _))
    exact hmap ⟨h, hh, rfl⟩
  have hnorm : P₂ ≤ Subgroup.normalizer ((Pz ⊔ P₁ : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwd h, fun hh => ?_⟩
    have h3 : d.x * (d.x * (d.x * h * d.x⁻¹) * d.x⁻¹) * d.x⁻¹ = h := by
      have : d.x * d.x * d.x = 1 := by
        have := hx3; rwa [pow_succ, pow_succ, pow_one] at this
      calc d.x * (d.x * (d.x * h * d.x⁻¹) * d.x⁻¹) * d.x⁻¹
          = (d.x * d.x * d.x) * h * (d.x * d.x * d.x)⁻¹ := by group
        _ = h := by rw [this]; group
    rw [← h3]
    exact hfwd _ (hfwd _ hh)
  have hsetK := Subgroup.coe_mul_of_right_le_normalizer_left (Pz ⊔ P₁) P₂ hnorm
  have hKP : (Pz ⊔ P₁) ⊔ P₂ = P := by
    apply le_antisymm (sup_le (sup_le hPzP hP₁P) hP₂P)
    set K : Subgroup (MulAut ↥V) := (Pz ⊔ P₁) ⊔ P₂ with hK
    have hNK : Pz ⊔ P₁ ≤ K := le_sup_left
    have hKP' : K ≤ P := sup_le (sup_le hPzP hP₁P) hP₂P
    have h9 : 9 ∣ Nat.card K := hcN ▸ Subgroup.card_dvd_of_le hNK
    have hdK : Nat.card K ∣ 3 ^ 3 := by
      have := Subgroup.card_dvd_of_le hKP'
      rwa [hcP] at this
    obtain ⟨m, hm3, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdK
    have hxK : d.x ∈ K := (le_sup_right : P₂ ≤ K) (Subgroup.mem_zpowers _)
    have hK27 : Nat.card K = 27 := by
      interval_cases m
      · omega
      · omega
      · exfalso
        have hKN : Pz ⊔ P₁ = K :=
          Subgroup.eq_of_le_of_card_ge hNK (by rw [hcN, hm]; norm_num)
        exact hxN (hKN ▸ hxK)
      · rw [hm]; norm_num
    exact (Subgroup.eq_of_le_of_card_ge hKP' (by rw [hK27, hcP])).symm.le
  calc (Pz : Set (MulAut ↥V)) * (P₁ : Set (MulAut ↥V)) * (P₂ : Set (MulAut ↥V))
      = ((Pz ⊔ P₁ : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) * (P₂ : Set (MulAut ↥V)) := by
        rw [hsetN]
    _ = (((Pz ⊔ P₁) ⊔ P₂ : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) := hsetK.symm
    _ = (P : Set (MulAut ↥V)) := by rw [hKP]


theorem tau_inv_zpowers [Finite G] {c : MulAut V} (hc : c = d.x ∨ c = d.y) :
    ∀ a ∈ Subgroup.zpowers c, d.τ * a * d.τ⁻¹ = a⁻¹ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  intro a ha
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [← conj_zpow]
  rcases hc with rfl | rfl
  · rw [d.gen.tau_x, inv_zpow]
  · rw [d.gen.tau_y, inv_zpow]

end Seven7Data

theorem Seven7Data.seven1516P_of [Finite G] {T Mc M : Subgroup G}
    {hVe : IsElemAbelian 2 (V154 T Mc M)} (d : Seven7Data (V154 T Mc M) M T hVe)
    (hA₀ : mBar0 T Mc M =
      oTwoUpper (autOn M (V154 T Mc M)) ⊔ Subgroup.zpowers d.tt) :
    Seven1516P T Mc M d.Z₁ d.Z₂ d.V₂ := by
  let _ : CommGroup ↥(V154 T Mc M) := commGroupOfElemAbelian hVe
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 := SevenGen.y3 d.ctx d.gen
  have hx3 := SevenGen.x3 d.ctx d.gen
  have hz1 : d.z ≠ 1 := d.gen.z1
  have hy1 : d.y ≠ 1 := SevenGen.y_ne_one d.gen
  have hx1 : d.x ≠ 1 := fun hx => hz1 (by rw [d.gen.zdef, hx]; group)
  refine ⟨?_, Subgroup.zpowers d.y, Subgroup.zpowers d.x, card_pow_gen hy3 hy1,
    card_pow_gen hx3 hx1, ?_, ?_, ?_, ?_, d.Z₁_eq_inf_centralizer,
    d.Z₂_eq_inf_centralizer, d.V₂_eq_commutator⟩
  · rw [d.pCore_eq_oTwoUpper]
    exact d.ctx.P1
  · rw [hA₀]
    exact le_sup_of_le_left (Subgroup.zpowers_le.mpr d.gen.yP)
  · rw [hA₀]
    exact le_sup_of_le_left (Subgroup.zpowers_le.mpr d.gen.xP)
  · refine ⟨d.τ, ?_, d.tau_inv_zpowers (Or.inr rfl), d.tau_inv_zpowers (Or.inl rfl)⟩
    have hTM : T ≤ M := d.hsyl.1
    have h1 : T ⊓ m0Of T Mc M = preOn T (V154 T Mc M) (mBar0 T Mc M) := by
      ext x
      simp only [Subgroup.mem_inf, m0Of, mem_preOn]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hTM h.1, h.2⟩⟩
    rw [h1, autOn_preOn_inf, hA₀, inf_comm]
    have := SevenGen.inf_A₀ d.ctx d.gen d.hp d.htp
    rw [this]
    exact Subgroup.mem_zpowers _
  · rw [d.pCore_eq_oTwoUpper]
    exact d.center_mul_zpowers_mul


end CFSG.Quasithin
