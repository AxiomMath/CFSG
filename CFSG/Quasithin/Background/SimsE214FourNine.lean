module

public import CFSG.Quasithin.Background.SimsE214FourNineY

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace E214F

variable {Γ : Type} [Group Γ] [Finite Γ] {X T M V : Subgroup Γ} {g : Γ}

theorem mem_B_of_commutator_mem (hp : E2.Pair X T M V g) (hJ : pCoreOf 2 X = kerIn M X)
    {v : Γ} (hv : v ∈ V)
    (hge : E2.star M X (B6.conjSub g V) ⊔
      Subgroup.zpowers (E2P.starMap M X ⟨v, hp.V_le hv⟩) = ⊤) :
    ∀ p ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V),
      v * p * v⁻¹ * p⁻¹ ∈ V ⊓ B6.conjSub g V → p ∈ kerIn M X ⊓ V := by
  set Z := V ⊓ B6.conjSub g V with hZdef
  have hJ2 : IsPGroup 2 (pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hJX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hZc : ∀ z ∈ Z, ∀ y ∈ X, z * y = y * z := fun z hz y hy => hp.mem_center hz hy
  have hvX : v ∈ X := hp.V_le hv
  have hgen2 : X ≤ (B6.conjSub g V ⊔ Subgroup.zpowers v) ⊔ pCoreOf 2 X := by
    rw [hJ]
    exact le_sup_zpowers_sup_kerIn hp.conj_le hvX hge
  have hL2 := fixed_of_sup hJ2 hJX hp.P_le_pCoreOf hp.le_normalizer_P hZc
    (fun p hp' q hq => (hp.commutator_sq_mem_Z hp' hq).1)
    (fun y hy j hj => hp.commutator_mem_P_of_mem_pCoreOf hy hj) (fixed_of_pair hp)
    (sup_le hp.conj_le (Subgroup.zpowers_le.mpr hvX)) hgen2
  intro p hpP hpv
  obtain ⟨b, hb, a, ha, rfl⟩ := hp.mem_P_iff.mp hpP
  have hbX : b ∈ X := (hp.P_le_pCoreOf.trans hJX) (Subgroup.mem_sup_left hb)
  have hva : v * a * v⁻¹ * a⁻¹ ∈ Z := by
    have e1 : v * (b * a) * v⁻¹ * (b * a)⁻¹ = b * (v * a * v⁻¹ * a⁻¹) * b⁻¹ := by
      calc v * (b * a) * v⁻¹ * (b * a)⁻¹ = (v * b) * a * v⁻¹ * a⁻¹ * b⁻¹ := by group
        _ = (b * v) * a * v⁻¹ * a⁻¹ * b⁻¹ := by rw [hp.comm hv hb.2]
        _ = b * (v * a * v⁻¹ * a⁻¹) * b⁻¹ := by group
    rw [e1] at hpv
    have hc := hZc _ hpv b⁻¹ (X.inv_mem hbX)
    have e2 : v * a * v⁻¹ * a⁻¹ = b⁻¹ * (b * (v * a * v⁻¹ * a⁻¹) * b⁻¹) * b := by group
    rw [e2, ← hc, inv_mul_cancel_right]
    exact hpv
  have haZ : a ∈ Z := by
    refine hL2 a (Subgroup.mem_sup_right ha) fun l hl => ?_
    have haV : a ∈ B6.conjSub g V := (B6.conjSub g).monotone inf_le_right ha
    have hVF : B6.conjSub g V ≤ fixModSubgroup X Z hZc a := fun w hw =>
      ⟨hp.conj_le hw, by
        rw [hp.comm_conj hw haV, mul_inv_cancel_right, mul_inv_cancel]; exact Z.one_mem⟩
    have hvF : Subgroup.zpowers v ≤ fixModSubgroup X Z hZc a :=
      Subgroup.zpowers_le.mpr ⟨hvX, hva⟩
    exact ((sup_le hVF hvF) hl).2
  exact (kerIn M X ⊓ V).mul_mem hb (hp.inf_conj_le_kerIn_inf haZ)

theorem fpf_of_inv_mul_mem (hp : E2.Pair X T M V g) {a b : Γ} (ha : a ∈ X) (hb : b ∈ X)
    (hao : Odd (orderOf a)) (hbo : Odd (orderOf b)) (hab : a⁻¹ * b ∈ pCoreOf 2 X)
    (hfa : ∀ p ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V),
      a * p * a⁻¹ * p⁻¹ ∈ V ⊓ B6.conjSub g V → p ∈ V ⊓ B6.conjSub g V) :
    ∀ p ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V),
      b * p * b⁻¹ * p⁻¹ ∈ V ⊓ B6.conjSub g V → p ∈ V ⊓ B6.conjSub g V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V) with hPdef
  set Z := V ⊓ B6.conjSub g V with hZdef
  have hJX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hPX : P ≤ X := hp.P_le_pCoreOf.trans hJX
  have hZfix : ∀ y ∈ X, ∀ z ∈ Z, y * z * y⁻¹ = z := fun y hy z hz => by
    rw [← hp.mem_center hz hy, mul_inv_cancel_right]
  let K : Subgroup Γ :=
    { carrier := {i | i ∈ X ∧ ∀ p ∈ P, i * p * i⁻¹ * p⁻¹ ∈ Z}
      mul_mem' := by
        rintro i₁ i₂ ⟨h₁, k₁⟩ ⟨h₂, k₂⟩
        refine ⟨X.mul_mem h₁ h₂, fun p hp' => ?_⟩
        have e1 : (i₁ * i₂) * p * (i₁ * i₂)⁻¹ * p⁻¹ =
            (i₁ * (i₂ * p * i₂⁻¹ * p⁻¹) * i₁⁻¹) * (i₁ * p * i₁⁻¹ * p⁻¹) := by group
        rw [e1, hZfix i₁ h₁ _ (k₂ p hp')]
        exact Z.mul_mem (k₂ p hp') (k₁ p hp')
      one_mem' := ⟨X.one_mem, fun p _ => by simp⟩
      inv_mem' := by
        rintro i ⟨hi, k⟩
        refine ⟨X.inv_mem hi, fun p hp' => ?_⟩
        have hp'' : i⁻¹ * p * i⁻¹⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp (hp.le_normalizer_P (X.inv_mem hi)) p).mp hp'
        have e1 : i⁻¹ * p * i⁻¹⁻¹ * p⁻¹ =
            (i * (i⁻¹ * p * i⁻¹⁻¹) * i⁻¹ * (i⁻¹ * p * i⁻¹⁻¹)⁻¹)⁻¹ := by group
        rw [e1]
        exact Z.inv_mem (k _ hp'') }
  have hKX : K ≤ X := fun i hi => hi.1
  have hXK : X ≤ Subgroup.normalizer (K : Set Γ) := by
    have key : ∀ y ∈ X, ∀ i ∈ K, y * i * y⁻¹ ∈ K := by
      rintro y hy i ⟨hi, k⟩
      refine ⟨X.mul_mem (X.mul_mem hy hi) (X.inv_mem hy), fun p hp' => ?_⟩
      have hp'' : y⁻¹ * p * y⁻¹⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hp.le_normalizer_P (X.inv_mem hy)) p).mp hp'
      have e1 : y * i * y⁻¹ * p * (y * i * y⁻¹)⁻¹ * p⁻¹ =
          y * (i * (y⁻¹ * p * y⁻¹⁻¹) * i⁻¹ * (y⁻¹ * p * y⁻¹⁻¹)⁻¹) * y⁻¹ := by group
      rw [e1, hZfix y hy _ (k _ hp'')]
      exact k _ hp''
    exact fun y hy => B6.mem_normalizer_of_forall_mem (key y hy)
      (fun i hi => by simpa using key y⁻¹ (X.inv_mem hy) i hi)
  have hKn : (K.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).2 hXK
  have hPK : ∀ q ∈ P, q ∈ K := fun q hq =>
    ⟨hPX hq, fun p hp' => (hp.commutator_sq_mem_Z hq hp').1⟩
  set j := a⁻¹ * b with hj
  have hjX : j ∈ X := hJX hab
  have hjK : j ∈ K := by
    let q := QuotientGroup.mk' (K.subgroupOf X)
    have hcomm : Commute (q ⟨a, ha⟩) (q ⟨j, hjX⟩) := by
      show q ⟨a, ha⟩ * q ⟨j, hjX⟩ = q ⟨j, hjX⟩ * q ⟨a, ha⟩
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have h1 := hp.commutator_mem_P_of_mem_pCoreOf (X.inv_mem ha) ((pCoreOf 2 X).inv_mem hab)
      have e1 : ((((⟨a, ha⟩ : X) * ⟨j, hjX⟩)⁻¹ * (⟨j, hjX⟩ * ⟨a, ha⟩) : X) : Γ) =
          (a⁻¹ * j⁻¹ * a⁻¹⁻¹ * j⁻¹⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e1]
      exact hPK _ (P.inv_mem h1)
    set n := orderOf a * orderOf b with hn
    have hab' : (⟨b, hb⟩ : X) = ⟨a, ha⟩ * ⟨j, hjX⟩ := Subtype.ext (by
      simp only [Subgroup.coe_mul, hj]
      group)
    have hqj : q ⟨j, hjX⟩ ^ n = 1 := by
      have h1 : (q ⟨a, ha⟩ * q ⟨j, hjX⟩) ^ n = 1 := by
        rw [← map_mul, ← hab', ← map_pow, hn, mul_comm, pow_mul]
        have : (⟨b, hb⟩ : X) ^ orderOf b = 1 := by
          apply Subtype.ext
          simp [pow_orderOf_eq_one]
        rw [this, one_pow, map_one]
      rw [hcomm.mul_pow] at h1
      have h2 : q ⟨a, ha⟩ ^ n = 1 := by
        rw [← map_pow, hn, pow_mul]
        have : (⟨a, ha⟩ : X) ^ orderOf a = 1 := by
          apply Subtype.ext
          simp [pow_orderOf_eq_one]
        rw [this, one_pow, map_one]
      rw [h2, one_mul] at h1
      exact h1
    have hjn : j ^ n ∈ K := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at hqj
      simpa using hqj
    obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X ⟨j, hab⟩
    have hjm : j ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine B6.mem_of_pow_mem_of_coprime hjn ?_
    have hn2 : Nat.Coprime (2 ^ m) n :=
      Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr (hao.mul hbo))
    exact hn2.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hjm)
  intro p hpP hpb
  refine hfa p hpP ?_
  have h1 := hjK.2 p hpP
  have hb' : b = a * j := by rw [hj]; group
  rw [hb'] at hpb
  have e1 : a * j * p * (a * j)⁻¹ * p⁻¹ =
      (a * (j * p * j⁻¹ * p⁻¹) * a⁻¹) * (a * p * a⁻¹ * p⁻¹) := by group
  rw [e1, hZfix a ha _ h1] at hpb
  have e2 : a * p * a⁻¹ * p⁻¹ = (j * p * j⁻¹ * p⁻¹)⁻¹ *
      ((j * p * j⁻¹ * p⁻¹) * (a * p * a⁻¹ * p⁻¹)) := by group
  rw [e2]
  exact Z.mul_mem (Z.inv_mem h1) hpb

theorem fpf_of_star_eq (hp : E2.Pair X T M V g) (hJ : pCoreOf 2 X = kerIn M X) {v : Γ}
    (hv : v ∈ V)
    (hCv : ∀ p ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V),
      v * p * v⁻¹ * p⁻¹ ∈ V ⊓ B6.conjSub g V → p ∈ kerIn M X ⊓ V)
    {x u w : Γ} (hx : x ∈ X) (hxo : Odd (orderOf x)) (hu : u ∈ X) (hw : w ∈ X)
    (hπ : E2P.starMap M X ⟨u * x * u⁻¹, X.mul_mem (X.mul_mem hu hx) (X.inv_mem hu)⟩ =
      E2P.starMap M X ⟨v * (w * v * w⁻¹),
        X.mul_mem (hp.V_le hv) (X.mul_mem (X.mul_mem hw (hp.V_le hv)) (X.inv_mem hw))⟩)
    (hgen : E2.star M X V ⊔ E2.star M X (B6.conjSub w V) = ⊤) :
    ∀ p ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V),
      x * p * x⁻¹ * p⁻¹ ∈ V ⊓ B6.conjSub g V → p ∈ V ⊓ B6.conjSub g V := by
  set P := (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V) with hPdef
  set Z := V ⊓ B6.conjSub g V with hZdef
  have hJ2 : IsPGroup 2 (pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hJX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hPX : P ≤ X := hp.P_le_pCoreOf.trans hJX
  have hZc : ∀ z ∈ Z, ∀ y ∈ X, z * y = y * z := fun z hz y hy => hp.mem_center hz hy
  have hZfix : ∀ y ∈ X, ∀ z ∈ Z, y * z * y⁻¹ = z := fun y hy z hz => by
    rw [← hZc z hz y hy, mul_inv_cancel_right]
  have hvX : v ∈ X := hp.V_le hv
  have hwVX : B6.conjSub w V ≤ X := fun y hy => by
    rw [B6.mem_conjSub] at hy
    have := X.mul_mem (X.mul_mem hw (hp.V_le hy)) (X.inv_mem hw)
    simpa [mul_assoc] using this
  set e := w * v * w⁻¹ with he
  have heX : e ∈ X := X.mul_mem (X.mul_mem hw hvX) (X.inv_mem hw)
  have hgenX : X ≤ (V ⊔ B6.conjSub w V) ⊔ pCoreOf 2 X := by
    rw [hJ]
    refine le_sup_kerIn ?_
    rw [star_sup hp.V_le hwVX]
    exact hgen
  have hL := fixed_of_sup hJ2 hJX hp.P_le_pCoreOf hp.le_normalizer_P hZc
    (fun p hp' q hq => (hp.commutator_sq_mem_Z hp' hq).1)
    (fun y hy j hj => hp.commutator_mem_P_of_mem_pCoreOf hy hj) (fixed_of_pair hp)
    (sup_le hp.V_le hwVX) hgenX
  have hve : ∀ p ∈ P, v * p * v⁻¹ * p⁻¹ ∈ Z → e * p * e⁻¹ * p⁻¹ ∈ Z → p ∈ Z := by
    intro p hpP hpv hpe
    have hpB := hCv p hpP hpv
    have hp' : w⁻¹ * p * w ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (hp.le_normalizer_P (X.inv_mem hw)) p).mp hpP
      rwa [inv_inv] at this
    have hp'v : v * (w⁻¹ * p * w) * v⁻¹ * (w⁻¹ * p * w)⁻¹ ∈ Z := by
      have e1 : v * (w⁻¹ * p * w) * v⁻¹ * (w⁻¹ * p * w)⁻¹ =
          w⁻¹ * (e * p * e⁻¹ * p⁻¹) * w⁻¹⁻¹ := by rw [he]; group
      rw [e1, hZfix w⁻¹ (X.inv_mem hw) _ hpe]
      exact hpe
    have hp'B := hCv _ hp' hp'v
    refine hL p hpP fun l hl => ?_
    have hVF : V ≤ fixModSubgroup X Z hZc p := fun y hy =>
      ⟨hp.V_le hy, by rw [hp.comm hy hpB.2, mul_inv_cancel_right, mul_inv_cancel]; exact Z.one_mem⟩
    have hWF : B6.conjSub w V ≤ fixModSubgroup X Z hZc p := fun y hy => by
      refine ⟨hwVX hy, ?_⟩
      rw [B6.mem_conjSub] at hy
      have h1 := hp.comm hy hp'B.2
      have e1 : y * p * y⁻¹ * p⁻¹ =
          w * ((w⁻¹ * y * w) * (w⁻¹ * p * w) * (w⁻¹ * y * w)⁻¹ * (w⁻¹ * p * w)⁻¹) * w⁻¹ := by
        group
      rw [e1, h1, mul_inv_cancel_right, mul_inv_cancel, mul_one, mul_inv_cancel]
      exact Z.one_mem
    exact ((sup_le hVF hWF) hl).2
  have hv2 : v * v = 1 := by rw [← pow_two]; exact hp.elem.2 v hv
  have he2 : e * e = 1 := by
    calc e * e = w * (v * v) * w⁻¹ := by rw [he]; group
      _ = 1 := by rw [hv2]; group
  obtain ⟨x', hx'z, hx'o, hx'fpf⟩ := exists_fpf_of_pair hvX heX hv2 he2
    (hJ2.to_le hp.P_le_pCoreOf) hPX hp.le_normalizer_P hZc hve
  obtain ⟨j₀, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'z
  set y := u * x * u⁻¹ with hy
  have hyX : y ∈ X := X.mul_mem (X.mul_mem hu hx) (X.inv_mem hu)
  have hyo : Odd (orderOf y) := by
    rw [hy, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hxo
  have hyjo : Odd (orderOf (y ^ j₀)) := by
    refine Odd.of_dvd_nat hyo (orderOf_dvd_of_pow_eq_one ?_)
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
      one_zpow]
  have hve' : v * e ∈ X := X.mul_mem hvX heX
  have hπj : E2P.starMap M X ⟨(v * e) ^ j₀, X.zpow_mem hve' j₀⟩ =
      E2P.starMap M X ⟨y ^ j₀, X.zpow_mem hyX j₀⟩ := by
    have e1 : (⟨(v * e) ^ j₀, X.zpow_mem hve' j₀⟩ : X) = (⟨v * e, hve'⟩ : X) ^ j₀ :=
      Subtype.ext (by simp)
    have e2 : (⟨y ^ j₀, X.zpow_mem hyX j₀⟩ : X) = (⟨y, hyX⟩ : X) ^ j₀ :=
      Subtype.ext (by simp)
    rw [e1, e2, map_zpow, map_zpow]
    congr 1
    exact hπ.symm
  have hmem : ((v * e) ^ j₀)⁻¹ * y ^ j₀ ∈ pCoreOf 2 X := by
    rw [E2P.starMap, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hπj
    rw [hJ]
    simpa using hπj
  have hyfpf := fpf_of_inv_mul_mem hp (X.zpow_mem hve' j₀) (X.zpow_mem hyX j₀) hx'o hyjo hmem
    hx'fpf
  intro p hpP hpx
  have hp' : u * p * u⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hp.le_normalizer_P hu) p).mp hpP
  have hyp : y * (u * p * u⁻¹) * y⁻¹ * (u * p * u⁻¹)⁻¹ ∈ Z := by
    have e1 : y * (u * p * u⁻¹) * y⁻¹ * (u * p * u⁻¹)⁻¹ = u * (x * p * x⁻¹ * p⁻¹) * u⁻¹ := by
      rw [hy]; group
    rw [e1, hZfix u hu _ hpx]
    exact hpx
  have hyF : y ∈ fixModSubgroup X Z hZc (u * p * u⁻¹) := ⟨hyX, hyp⟩
  have h1 := hyfpf _ hp' ((fixModSubgroup X Z hZc (u * p * u⁻¹)).zpow_mem hyF j₀).2
  have e2 : p = u⁻¹ * (u * p * u⁻¹) * u⁻¹⁻¹ := by group
  rw [e2, hZfix u⁻¹ (X.inv_mem hu) _ h1]
  exact h1

end E214F

open E214F

theorem e214NineSz_holds :
    E214NineSz := by
  intro Γ _ _ H T M V h _hc hTI I g hI hg hIV hZ k hk1 hSz X hXM hXc
  have := E2P.finite_starQuot (M ⊓ I) I
  have e : conjSubgroup V g = B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g
  have hgen : I = V ⊔ B6.conjSub g⁻¹ V := e ▸ hIV
  obtain ⟨hp, hVZ, -, -, hJ, -⟩ := RonanE211.e2_11C_all E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds h (E213M.noRoot_of_isInIHTV hI) (I.inv_mem hg) hgen
  obtain ⟨hk3, -⟩ := E2.card_of_isSz hSz
  have hk : 2 ≤ k := by omega
  have hsyl := hI.2.2.1
  have hTMI : T ⊓ I ≤ M ⊓ I := inf_le_inf_right I h.minParabolic.le
  have h1 := E214.inf_eq_inf_normalizer h hTI hI hg hIV hZ
  have hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set Γ) := h1.le.trans inf_le_right
  have hBorel := E214.isBorelIn_of_psl_or_sz hI hk (Or.inr hSz)
  obtain ⟨-, hVeq⟩ := E2.star_eq_center_of_psl_or_sz E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds hp hsyl hTMI (I.inv_mem hg) hgen hVZ hMN hBorel hk (Or.inr hSz)
  have hs : IsSimpleGroup (E2.StarQuot (M ⊓ I) I) := E2.isSimpleGroup_of_psl_or_sz (Or.inr hSz)
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ∉ kerIn (M ⊓ I) I := by
    have hne := E2.star_ne_bot_of_gen (M' := M ⊓ I) (I.inv_mem hg) hgen
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hw1' : w ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
    rw [E2P.star_def] at hw
    obtain ⟨x, hx, hxw⟩ := Subgroup.mem_map.mp hw
    refine ⟨x, Subgroup.mem_subgroupOf.mp hx, fun hxJ => hw1' ?_⟩
    rw [← hxw, E2P.starMap, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact hxJ
  have he : g⁻¹ * v * g⁻¹⁻¹ ∈ B6.conjSub g⁻¹ V := by
    rw [B6.mem_conjSub]
    simpa [mul_assoc] using hv
  obtain ⟨hcen, hCv⟩ := center_eq_bot_and_centralizer_le_of_sz hp hSz hVeq hv hv1
  obtain ⟨-, hge⟩ := gen_of_centralizer_le hp hcen hVeq hv hCv he
  have hCvB := mem_B_of_commutator_mem hp hJ hv hge
  set π := E2P.starMap (M ⊓ I) I with hπ
  set S := E2.star (M ⊓ I) I (T ⊓ I) with hSdef
  have hS : IsSylowTwoOf S ⊤ := E2.isSylowTwoOf_star_inf (M := M) hp.sylow
  set W := S ⊓ Subgroup.centralizer (S : Set (E2.StarQuot (M ⊓ I) I)) with hWdef
  have hVW : E2.star (M ⊓ I) I V = W := hVeq
  set h₀ : E2.StarQuot (M ⊓ I) I := (π ⟨g⁻¹, I.inv_mem hg⟩)⁻¹ with hh₀
  have hW' : E2.star (M ⊓ I) I (B6.conjSub g⁻¹ V) = W.map (MulAut.conj h₀⁻¹).toMonoidHom := by
    rw [star_conjSub (I.inv_mem hg) hp.V_le, hVW, hh₀, inv_inv]
  have hgenY : W ⊔ W.map (MulAut.conj h₀⁻¹).toMonoidHom = ⊤ := by
    rw [← hW', ← hVW, ← star_sup hp.V_le hp.conj_le, ← hp.gen]
    exact E2P.star_top _ _
  have hW2 : ∀ w ∈ W, w * w = 1 := fun w hw =>
    E2.sq_eq_one_of_mem_star (M := M) (I := I) hp.elem (hVW ▸ hw)
  have hv'W : π ⟨v, hp.V_le hv⟩ ∈ W := by
    rw [← hVW, E2P.star_def]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hv)
  have hv'1 : π ⟨v, hp.V_le hv⟩ ≠ 1 := by
    rw [hπ, E2P.starMap, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact hv1
  have hXI : X ≤ I := hXM.trans inf_le_right
  have hXN : E2.star (M ⊓ I) I X ≤ Subgroup.normalizer (S : Set (E2.StarQuot (M ⊓ I) I)) := by
    rw [← E2.star_eq_normalizer_of_isBorelIn hTMI hsyl hBorel, E2P.star_def, E2P.star_def]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono I hXM)
  have hXodd : Odd (Nat.card X) := by
    rw [hXc]
    exact Ch3E213M.odd_two_pow_sub_one (by omega)
  have hXJ : kerIn (M ⊓ I) I ⊓ X = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => (Subgroup.mem_bot).mpr ?_
    by_contra hz1
    have hzo : Odd (orderOf z) := Odd.of_dvd_nat hXodd (Subgroup.orderOf_dvd_natCard X hz.2)
    exact E214.not_mem_pCoreOf_of_odd hz1 hzo (hJ ▸ hz.1)
  have hXc' : Nat.card (E2.star (M ⊓ I) I X) = 2 ^ k - 1 := by
    rw [E2.card_star_of_le hXI, hXJ, Subgroup.relIndex_bot_left, hXc]
  obtain ⟨x₀, hx₀X, hx₀1, hx₀o⟩ := E214.exists_ne_one_odd_of_card hk1 hXc
  have hx₀I : x₀ ∈ I := hXI hx₀X
  have hx₀' : π ⟨x₀, hx₀I⟩ ∈ E2.star (M ⊓ I) I X := by
    rw [E2P.star_def]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx₀X)
  have hx₀'1 : π ⟨x₀, hx₀I⟩ ≠ 1 := by
    rw [hπ, E2P.starMap, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, ← hJ]
    exact E214.not_mem_pCoreOf_of_odd hx₀1 hx₀o
  obtain ⟨u', w', hux, hgenw⟩ :=
    exists_conj_eq_mul_of_isSz hSz hS hW2 hgenY hcen hv'W hv'1 hXN hXc' hx₀' hx₀'1
  obtain ⟨⟨u, huI⟩, rfl⟩ := E2P.starMap_surjective (M ⊓ I) I u'
  obtain ⟨⟨w, hwI⟩, rfl⟩ := E2P.starMap_surjective (M ⊓ I) I w'
  have hgenw' : E2.star (M ⊓ I) I V ⊔ E2.star (M ⊓ I) I (B6.conjSub w V) = ⊤ := by
    rw [star_conjSub hwI hp.V_le, hVW]
    exact hgenw
  have hfpf := fpf_of_star_eq hp hJ hv hCvB hx₀I hx₀o huI hwI (by
      show π (⟨u, huI⟩ * ⟨x₀, hx₀I⟩ * ⟨u, huI⟩⁻¹) =
        π (⟨v, hp.V_le hv⟩ * (⟨w, hwI⟩ * ⟨v, hp.V_le hv⟩ * ⟨w, hwI⟩⁻¹))
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv]
      exact hux) hgenw'
  intro b hb
  obtain ⟨⟨hbV, hbO⟩, hbC⟩ := hb
  have hbB : b ∈ kerIn (M ⊓ I) I ⊓ V := by
    rw [hp.kerIn_inf_eq]
    exact ⟨hbV, hbO⟩
  have h2 : x₀ * b * x₀⁻¹ * b⁻¹ ∈ V ⊓ B6.conjSub g⁻¹ V := by
    rw [Subgroup.mem_centralizer_iff.mp hbC x₀ hx₀X, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  rw [e]
  exact hfpf b (Subgroup.mem_sup_left hbB) h2

end CFSG.Quasithin.SimsE2
