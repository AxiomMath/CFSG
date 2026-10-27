module

public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4C
public import CFSG.Quasithin.Vol2.KGFactC31KG443Spor
public import CFSG.Quasithin.Vol2.KGFactC31NoM22Lie
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M24
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Layer0J4
public import CFSG.CGT.T75Q.OrdersSL
public import CFSG.Sporadic.He
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.Quasithin.KGC31.KG443

open Function CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped commutatorElement MatrixGroups

@[expose] def conjAut {X : Type*} [Group X] (Lb : Subgroup X) {b : X}
    (hb : b ∈ Subgroup.normalizer (Lb : Set X)) : MulAut ↥Lb where
  toFun x := ⟨b * x * b⁻¹, (Subgroup.mem_normalizer_iff.mp hb x).mp x.2⟩
  invFun x := ⟨b⁻¹ * x * b, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb) x).mp x.2
    simpa using this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjAut_apply {X : Type*} [Group X] (Lb : Subgroup X) {b : X}
    (hb : b ∈ Subgroup.normalizer (Lb : Set X)) (x : ↥Lb) :
    ((conjAut Lb hb x : ↥Lb) : X) = b * x * b⁻¹ := rfl

theorem conjAut_pow_apply {X : Type*} [Group X] (Lb : Subgroup X) {b : X}
    (hb : b ∈ Subgroup.normalizer (Lb : Set X)) (n : ℕ) (x : ↥Lb) :
    ((((conjAut Lb hb) ^ n) x : ↥Lb) : X) = b ^ n * x * (b ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, conjAut_apply, ih, pow_succ']
    group

theorem centralizes_of_inner {X : Type*} [Group X] [Finite X] {Lb : Subgroup X}
    (hZ : Subgroup.center ↥Lb = ⊥) (hinner : ∀ α : MulAut ↥Lb, ∃ g : ↥Lb, α = MulAut.conj g)
    {Y : Subgroup ↥Lb} {b : X} (hbN : b ∈ Subgroup.normalizer (Lb : Set X))
    (hbY : ∀ y ∈ Y, b * ((y : ↥Lb) : X) = ((y : ↥Lb) : X) * b)
    (hb6 : Nat.Coprime (orderOf b) 6)
    (hno : ∀ l : ↥Lb, (∀ y ∈ Y, l * y = y * l) → ∀ r : ℕ, r.Prime → 5 ≤ r → orderOf l = r →
      False) :
    ∀ x ∈ Lb, b * x = x * b := by
  obtain ⟨l, hl⟩ := hinner (conjAut Lb hbN)
  have hconj : ∀ x : ↥Lb, l * x * l⁻¹ = conjAut Lb hbN x := fun x => by
    rw [hl, MulAut.conj_apply]
  have hlY : ∀ y ∈ Y, l * y = y * l := by
    intro y hy
    have h1 : conjAut Lb hbN y = y := Subtype.ext (by
      rw [conjAut_apply, hbY y hy, mul_inv_cancel_right])
    rw [← hconj] at h1
    calc l * y = l * y * l⁻¹ * l := by group
      _ = y * l := by rw [h1]
  have hlb : orderOf l ∣ orderOf b := by
    apply orderOf_dvd_of_pow_eq_one
    have h2 : l ^ orderOf b ∈ Subgroup.center ↥Lb := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 : ((((conjAut Lb hbN) ^ orderOf b) g : ↥Lb) : X) = g := by
        rw [conjAut_pow_apply, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
      rw [hl, ← map_pow, MulAut.conj_apply] at h3
      have h4 : l ^ orderOf b * g * (l ^ orderOf b)⁻¹ = g := Subtype.ext h3
      calc g * l ^ orderOf b = l ^ orderOf b * g * (l ^ orderOf b)⁻¹ * l ^ orderOf b := by
            rw [h4]
        _ = l ^ orderOf b * g := by group
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  have hl1 : l = 1 := by
    by_contra hne
    have hne1 : orderOf l ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    obtain ⟨r, hr, hrl⟩ := Nat.exists_prime_and_dvd hne1
    have hr6 : Nat.Coprime r 6 := Nat.Coprime.coprime_dvd_left (hrl.trans hlb) hb6
    have hr5 : 5 ≤ r := by
      by_contra h
      have h2 := hr.two_le
      interval_cases r
      · exact absurd hr6 (by decide)
      · exact absurd hr6 (by decide)
      · exact absurd hr (by decide)
    have hl0 : orderOf l ≠ 0 := (orderOf_pos l).ne'
    refine hno (l ^ (orderOf l / r)) (fun y hy => ?_) r hr hr5 (orderOf_pow_orderOf_div hl0 hrl)
    exact (Commute.pow_left (hlY y hy) _).eq
  intro x hx
  have h1 := hconj ⟨x, hx⟩
  rw [hl1, one_mul, inv_one, mul_one] at h1
  have h2 : b * x * b⁻¹ = x := (congrArg Subtype.val h1).symm
  calc b * x = b * x * b⁻¹ * b := by group
    _ = x * b := by rw [h2]

variable {G : Type} [Group G] [Finite G]

theorem comm_le_pCoreOf {H L B : Subgroup G} (hLH : L ≤ H) (hBH : B ≤ H)
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h : ∀ x (hx : x ∈ L) b (hb : b ∈ B),
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hLH hx⟩ *
          QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨b, hBH hb⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨b, hBH hb⟩ *
          QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hLH hx⟩) :
    ⁅L, B⁆ ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Subgroup.commutator_le]
  intro x hx b hb
  have hc : ⁅x, b⁆ ∈ L := by
    rw [commutatorElement_def]
    have hbx : b * x⁻¹ * b⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hBN hb) x⁻¹).mp (L.inv_mem hx)
    have := L.mul_mem hx hbx
    simpa [mul_assoc] using this
  have hcH : ⁅x, b⁆ ∈ pCoreOf 2 H := by
    have hk : (⟨⁅x, b⁆, hLH hc⟩ : ↥H) = ⁅(⟨x, hLH hx⟩ : ↥H), ⟨b, hBH hb⟩⁆ := rfl
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨⁅x, b⁆, hLH hc⟩ : ↥H) = 1 := by
      rw [hk, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, h x hx b hb]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, rfl⟩
  have hpH : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hnormO : L ≤ Subgroup.normalizer ((L ⊓ pCoreOf 2 H : Subgroup G) : Set G) := by
    intro y hy
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, ?_⟩
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hLH hy)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnormO
    (hpH.to_le inf_le_right) ⟨hc, hcH⟩

theorem card_of_isHat {X S : Type} [Group X] [Group S] (h : IsHat X S) :
    Nat.card X = 3 * Nat.card S := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup, h3,
    Nat.card_congr e.toEquiv, mul_comm]

theorem center_eq_bot_of_secOnto {S : Type} [Group S]
    [IsSimpleGroup S] (hsec : SecOnto S (NativeSporadic.Carrier .M22)) : Subgroup.center S = ⊥ := by
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal S _ _ (Subgroup.center S) inferInstance
    with h | h
  · exact h
  · exfalso
    obtain ⟨Y, φ, hφ⟩ := hsec
    obtain ⟨a, b, hab⟩ := not_comm_m22
    obtain ⟨y, rfl⟩ := hφ a
    obtain ⟨z, rfl⟩ := hφ b
    have hz : (z : S) ∈ Subgroup.center S := by rw [h]; exact Subgroup.mem_top _
    have hyz : y * z = z * y := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact Subgroup.mem_center_iff.mp hz (y : S))
    exact hab (by rw [← map_mul, hyz, map_mul])

theorem m24_or_j4_of_list
    (hLeaf : NoM22SectionLie) {S : Type} [Group S] [Finite S]
    (hdvd : 1330560 ∣ Nat.card S) (hsec : SecOnto S (NativeSporadic.Carrier .M22))
    (hlist : A23List S) :
    Nonempty (S ≃* NativeSporadic.Carrier .M24) ∨ Nonempty (S ≃* NativeSporadic.Carrier .J4) := by
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hcard : ∀ n : ℕ, Nat.card S = n → ¬ 1330560 ∣ n → False := fun n h hn => hn (h ▸ hdvd)
  rcases hlist with ⟨n, hn5, hn8, ⟨e⟩⟩ | hodd | hchar2 | ⟨n, hn, hpsl⟩ | ⟨s, hs, ⟨e⟩⟩
  · exfalso
    interval_cases n <;>
      exact hcard _ (by rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
        card_alternatingGroup, Fintype.card_fin]) (by decide)
  · exfalso
    obtain ⟨Y, φ, hφ⟩ := hsec
    exact hLeaf S (Or.inl (Or.inl hodd)) Y φ hφ
  · exfalso
    obtain ⟨Y, φ, hφ⟩ := hsec
    exact hLeaf S (Or.inl (Or.inr hchar2)) Y φ hφ
  · exfalso
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hpsl
    have hF2 : Nat.card F = 2 := by rw [hF]; norm_num
    have hc : Nat.card S = Nat.card (Matrix.SpecialLinearGroup (Fin n) F) := by
      rw [Nat.card_congr e.toEquiv, CFSG.CGT.T75Q.card_statedProj_of_card_two n hF2]
    rcases hn with rfl | rfl
    · exact hcard _ (hc.trans (CFSG.CGT.T75Q.card_SL_four_two hF2)) (by decide)
    · exact hcard _ (hc.trans (CFSG.CGT.T75Q.card_SL_five_two hF2)) (by decide)
  · have hc := Nat.card_congr e.toEquiv
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hcard _ (hc.trans CFSG.Sporadic.Mathieu.card_M11) (by decide)).elim
    · exact (hcard _ (hc.trans CFSG.Sporadic.Mathieu.card_M12) (by decide)).elim
    · exact (hcard _ (hc.trans CFSG.Sporadic.Mathieu.card_M22) (by decide)).elim
    · exact (hcard _ (hc.trans CFSG.Sporadic.Schreier.m23_card) (by decide)).elim
    · exact Or.inl ⟨e⟩
    · exact (hcard _ (hc.trans CFSG.Sporadic.J1.card_J1) (by decide)).elim
    · exact (hcard _ (hc.trans CFSG.Sporadic.J2.card_J2) (by decide)).elim
    · exact Or.inr ⟨e⟩
    · exact (hcard _ (hc.trans CFSG.Sporadic.HS.card_HS) (by decide)).elim
    · exact (hcard _ (hc.trans CFSG.Sporadic.He.fam_he_order.1) (by decide)).elim
    · exact (hcard _ (hc.trans CFSG.Sporadic.Ru.card_Ru) (by decide)).elim

theorem isHat_m22_of_case2 (hLeaf : NoM22SectionLie) {S : Type} [Group S] [Finite S]
    (hdvd : 1330560 ∣ Nat.card S) (hsec : SecOnto S (NativeSporadic.Carrier .M22))
    (hc2 : A36Case2List S) : IsHat S (NativeSporadic.Carrier .M22) := by
  rcases hc2 with hsl | hA6 | hA7 | hM
  · exfalso
    obtain ⟨Y, φ, hφ⟩ := hsec
    exact hLeaf S (Or.inr hsl) Y φ hφ
  · exfalso
    have hc : Nat.card S = 3 * Nat.card (alternatingGroup (Fin 6)) := card_of_isHat hA6
    rw [Nat.card_eq_fintype_card (α := alternatingGroup (Fin 6)), card_alternatingGroup,
      Fintype.card_fin] at hc
    rw [hc] at hdvd
    exact absurd hdvd (by decide)
  · exfalso
    have hc : Nat.card S = 3 * Nat.card (alternatingGroup (Fin 7)) := card_of_isHat hA7
    rw [Nat.card_eq_fintype_card (α := alternatingGroup (Fin 7)), card_alternatingGroup,
      Fintype.card_fin] at hc
    rw [hc] at hdvd
    exact absurd hdvd (by decide)
  · exact hM

theorem false_of_case34 {S : Type} [Group S] [Finite S]
    (hsec : SecOnto S (NativeSporadic.Carrier .M22)) (hc : A36Case3 S ∨ A36Case4 S) : False := by
  have : IsSimpleGroup (NativeSporadic.Carrier .M22) := isSimpleGroup_m22
  rcases hc with ⟨p, hp, hp3, -, ⟨eF⟩, ⟨-, ψ, hψ, hker, -⟩⟩ | ⟨-, hnil, ⟨e5⟩, -⟩
  · have : Fact p.Prime := ⟨hp⟩
    have hsol : Group.IsSolvable ↥ψ.ker := by
      refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
      have ha : (a : S) ∈ CFSG.fittingSubgroup S := hker ▸ a.2
      have hb : (b : S) ∈ CFSG.fittingSubgroup S := hker ▸ b.2
      have h1 : eF ⟨a, ha⟩ * eF ⟨b, hb⟩ = eF ⟨b, hb⟩ * eF ⟨a, ha⟩ := mul_comm _ _
      rw [← map_mul, ← map_mul] at h1
      have h2 : (a : S) * b = (b : S) * a := congrArg Subtype.val (eF.injective h1)
      exact h2
    exact not_secOnto_sl2 (by omega) (hsec.quot not_comm_m22 ψ hsol)
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    let ψ : S →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
      e5.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup S))
    have hker : ψ.ker = CFSG.fittingSubgroup S := by
      rw [MonoidHom.ker_comp_of_injective _ _ e5.injective, QuotientGroup.ker_mk']
    have hsol : Group.IsSolvable ↥ψ.ker := by rw [hker]; infer_instance
    exact not_secOnto_sl2 (p := 5) (by norm_num) (hsec.quot not_comm_m22 ψ hsol)

theorem kg443J4Loc_holds
    (hLeaf : NoM22SectionLie) : CFSG.Quasithin.H13.Ch4.G443J4.KG443J4Loc := by
  intro G _ _ H L K B hH _ _ hL hKL hK hBH hBN hB6 hBK
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hKH : K ≤ H := hKL.trans hLH
  refine comm_le_pCoreOf hLH hBH hBN ?_
  have hQ : SQTKHyp (↥H ⧸ CFSG.pCore 2 ↥H) := SQTKHyp.of_sqtkGroup ↥H hH
  have hA36 : A36Strong (modO2Image H L) :=
    H13.VolI.a36ForSQTK_holds _ hQ _ (modO2Image_mem_cComp hL)
  set N := CFSG.pCore 2 ↥H with hN
  set Lb := modO2Image H L with hLb
  let π : ↥H →* ↥H ⧸ N := QuotientGroup.mk' N
  have hmemL : ∀ x (hx : x ∈ L), π ⟨x, hLH hx⟩ ∈ Lb := fun x hx => ⟨⟨x, hLH hx⟩, hx, rfl⟩
  let fK : ↥K →* ↥Lb :=
    (π.comp (Subgroup.inclusion hKH)).codRestrict Lb fun k => hmemL k (hKL k.2)
  have hkerK : fK.ker ≤ CFSG.pCore 2 ↥K := by
    have hkp : IsPGroup 2 fK.ker := by
      intro x
      have hx : Subgroup.inclusion hKH (x : ↥K) ∈ N := by
        have h1 : ((fK x : ↥Lb) : ↥H ⧸ N) = 1 := by rw [MonoidHom.mem_ker.mp x.2]; rfl
        have h2 : ((Subgroup.inclusion hKH (x : ↥K) : ↥H) : ↥H ⧸ N) = 1 := h1
        exact (QuotientGroup.eq_one_iff _).mp h2
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hx⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : (Subgroup.inclusion hKH (x : ↥K)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      rw [← map_pow] at h1
      exact (Subgroup.inclusion_injective hKH) (by simpa using h1)
    exact le_sSup ⟨inferInstance, hkp⟩
  obtain ⟨-, hZ3, ⟨eK⟩⟩ := hK
  let qK : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' _
  have hqK : Surjective qK := QuotientGroup.mk'_surjective _
  have hkerq : fK.ker ≤ qK.ker := by rw [QuotientGroup.ker_mk']; exact hkerK
  let ψK : ↥K →* NativeSporadic.Carrier .M22 :=
    eK.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center _)).comp qK)
  have hψK : Surjective ψK := eK.surjective.comp ((QuotientGroup.mk'_surjective _).comp hqK)
  have hkerψ : fK.ker ≤ ψK.ker := fun k hk => by
    have h1 : qK k = 1 := hkerq hk
    show eK (QuotientGroup.mk' _ (qK k)) = 1
    rw [h1, map_one, map_one]
  obtain ⟨φ, hφ⟩ := exists_range_surj fK ψK hψK hkerψ
  obtain ⟨φ3, hφ3⟩ := exists_range_surj fK qK hqK hkerq
  have h3 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 1330560 := by
    rw [(Subgroup.center _).card_eq_card_quotient_mul_card_subgroup, hZ3,
      Nat.card_congr eK.toEquiv]
    exact congrArg (· * 3) CFSG.Sporadic.Mathieu.card_M22
  have hdvdR : 1330560 ∣ Nat.card ↥fK.range := h3 ▸ card_dvd_of_surjective hφ3
  have hdvd : 1330560 ∣ Nat.card ↥Lb := hdvdR.trans (Subgroup.card_subgroup_dvd_card _)
  have hsec : SecOnto ↥Lb (NativeSporadic.Carrier .M22) := ⟨fK.range, φ, hφ⟩
  have hbN : ∀ b (hb : b ∈ B), π ⟨b, hBH hb⟩ ∈ Subgroup.normalizer (Lb : Set (↥H ⧸ N)) := by
    intro b hb
    apply Subgroup.le_normalizer_map π
    refine ⟨⟨b, hBH hb⟩, Subgroup.mem_normalizer_iff.mpr fun h => ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hBN hb) h
  have hbK : ∀ b (hb : b ∈ B), ∀ y ∈ fK.range,
      π ⟨b, hBH hb⟩ * ((y : ↥Lb) : ↥H ⧸ N) = ((y : ↥Lb) : ↥H ⧸ N) * π ⟨b, hBH hb⟩ := by
    rintro b hb _ ⟨k, rfl⟩
    show π ⟨b, hBH hb⟩ * π ⟨k, hKH k.2⟩ = π ⟨k, hKH k.2⟩ * π ⟨b, hBH hb⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hBK hb) k k.2).symm
  have hb6 : ∀ b (hb : b ∈ B), Nat.Coprime (orderOf (π ⟨b, hBH hb⟩)) 6 := by
    intro b hb
    refine Nat.Coprime.coprime_dvd_left ?_ hB6
    refine (orderOf_map_dvd π _).trans ?_
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_dvd_natCard B hb
  suffices hcent : ∀ b (hb : b ∈ B), ∀ x ∈ Lb, π ⟨b, hBH hb⟩ * x = x * π ⟨b, hBH hb⟩ by
    intro x hx b hb
    exact (hcent b hb _ (hmemL x hx)).symm
  rcases hA36.1 with ⟨-, hsimp, hlist⟩ | ⟨-, -, hc2⟩ | hc3 | hc4
  ·
    have hZ : Subgroup.center ↥Lb = ⊥ := center_eq_bot_of_secOnto hsec
    intro b hb
    rcases m24_or_j4_of_list hLeaf hdvd hsec hlist with he | he
    · obtain ⟨e⟩ := he
      refine centralizes_of_inner hZ
        (CFSG.EvenSporadicStandard.HypOne.M24.allInner_of_isSporadic ⟨e⟩) (hbN b hb) (hbK b hb)
        (hb6 b hb) fun l hl r hr h5 hlr => ?_
      exact false_of_cent_m24 e hφ hl hr h5 hlr
    · obtain ⟨e⟩ := he
      refine centralizes_of_inner hZ
        (CFSG.EvenSporadicStandard.J4Std.allInner_of_isSporadic ⟨e⟩) (hbN b hb) (hbK b hb)
        (hb6 b hb) fun l hl r hr h5 hlr => ?_
      exact false_of_cent_j4 e hφ hl hr h5 hlr
  ·
    have hM := isHat_m22_of_case2 hLeaf hdvd hsec hc2
    have hcardL : Nat.card ↥Lb = 1330560 := by
      rw [card_of_isHat hM]
      exact congrArg (3 * ·) CFSG.Sporadic.Mathieu.card_M22
    have htop : fK.range = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _)
        (hcardL ▸ Nat.le_of_dvd Nat.card_pos hdvdR))
    intro b hb x hx
    have := hbK b hb ⟨x, hx⟩ (by rw [htop]; exact Subgroup.mem_top _)
    exact this
  · exact (false_of_case34 hsec (Or.inl hc3)).elim
  · exact (false_of_case34 hsec (Or.inr hc4)).elim

end CFSG.Quasithin.KGC31.KG443

end
