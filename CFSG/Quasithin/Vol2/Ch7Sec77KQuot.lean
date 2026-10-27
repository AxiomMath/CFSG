module

public import CFSG.Quasithin.Vol2.Ch7Sec77Mult
public import CFSG.RankThree.PartOne.S9.Extraction.Basic
public import CFSG.Quasithin.Vol2.Ch7Faith
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch7Sec77Mod

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem center_statedSL_two_eq_bot (m : ℕ) :
    Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) = ⊥ := by
  have h1 : Subgroup.center (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Subgroup.mem_bot]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Subsingleton.elim _ _
    · have hr1 : r = 1 := by
        rw [Fintype.card_fin] at hr
        rcases (by decide : ∀ r : ZMod 2, r = 0 ∨ r = 1) r with h | h
        · rw [h, zero_pow hm.ne'] at hr
          exact absurd hr (by decide)
        · exact h
      subst hr1
      apply Subtype.ext
      rw [← hrA]
      simp
  have h2 := Subgroup.map_center_eq (specialLinearGroupEquivStatedSL m (ZMod 2))
  rw [h1, Subgroup.map_bot] at h2
  exact h2.symm

theorem quot_equiv_of_autOn
    {K W : Subgroup G}
    (hKW : K ≤ Subgroup.normalizer (W : Set G)) (hperf : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K))
    {m : ℕ} (hm : m = 3 ∨ m = 4 ∨ m = 5)
    (eK : ↥(autOn K W) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)))
    (hO : pCoreOf 2 K ≤ Subgroup.centralizer (W : Set G))
    (hZ : ∀ c ∈ K ⊓ Subgroup.centralizer (W : Set G), ∀ k ∈ K, ⁅c, k⁆ ∈ pCoreOf 2 K) :
    K ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 K ∧
      Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := CFSG.QuasithinUnique.Setup.rho W K hKW with hρdef
  have hrange : ρ.range = autOn K W := CFSG.QuasithinUnique.Setup.range_rho hKW
  let ρ' : ↥K →* ↥(autOn K W) :=
    (MulEquiv.subgroupCongr hrange).toMonoidHom.comp ρ.rangeRestrict
  have hρ'v : ∀ k, ((ρ' k : ↥(autOn K W)) : MulAut ↥W) = ρ k := fun k => rfl
  have hρ's : Function.Surjective ρ' :=
    (MulEquiv.subgroupCongr hrange).surjective.comp ρ.rangeRestrict_surjective
  have hρ'1 : ∀ k, ρ' k = 1 ↔ (k : G) ∈ Subgroup.centralizer (W : Set G) := by
    intro k
    rw [← CFSG.QuasithinUnique.Setup.rho_eq_one_iff hKW k, ← hρ'v]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  have hpρ : CFSG.pCore 2 ↥K ≤ ρ'.ker := by
    intro k hk
    rw [MonoidHom.mem_ker, hρ'1]
    exact hO (coe_mem_pCoreOf hk)
  let ρb : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(autOn K W) := QuotientGroup.lift _ ρ' hpρ
  have hρbs : Function.Surjective ρb := by
    intro x
    obtain ⟨k, rfl⟩ := hρ's x
    exact ⟨QuotientGroup.mk k, rfl⟩
  have hZK : Subgroup.center ↥(autOn K W) = ⊥ := by
    have h1 := Subgroup.map_center_eq eK.symm
    rw [center_statedSL_two_eq_bot, Subgroup.map_bot] at h1
    exact h1.symm
  have hker : ρb.ker = Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
      have hk1 : ρ' k = 1 := hx
      have hkC : (k : G) ∈ K ⊓ Subgroup.centralizer (W : Set G) := ⟨k.2, (hρ'1 k).1 hk1⟩
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective y
      have h1 := hZ _ hkC _ k'.2
      have h2 : (⁅k, k'⁆ : ↥K) ∈ CFSG.pCore 2 ↥K := by
        obtain ⟨x', hx', hxx'⟩ := h1
        have e2 : x' = ⁅k, k'⁆ := Subtype.ext (by
          rw [show ((⁅k, k'⁆ : ↥K) : G) = ⁅(k : G), (k' : G)⁆ by simp [commutatorElement_def]]
          exact hxx')
        rw [← e2]
        exact hx'
      have h3 : (QuotientGroup.mk ⁅k, k'⁆ : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr h2
      rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv] at h3
      calc (QuotientGroup.mk k' : ↥K ⧸ CFSG.pCore 2 ↥K) * QuotientGroup.mk k
          = ((QuotientGroup.mk k : ↥K ⧸ CFSG.pCore 2 ↥K) * QuotientGroup.mk k' *
              (QuotientGroup.mk k)⁻¹ * (QuotientGroup.mk k')⁻¹)⁻¹ *
            (QuotientGroup.mk k * QuotientGroup.mk k') := by group
        _ = QuotientGroup.mk k * QuotientGroup.mk k' := by rw [h3, inv_one, one_mul]
    · intro x hx
      have h1 : ρb x ∈ Subgroup.center ↥(autOn K W) := by
        refine Subgroup.mem_center_iff.mpr fun y => ?_
        obtain ⟨x', rfl⟩ := hρbs y
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx x')]
      rw [hZK, Subgroup.mem_bot] at h1
      exact h1
  have eZ : (↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρb hρbs)).trans eK
  have hO2 : CFSG.pCore 2 (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    CFSG.RankThree.PartOne.Extract.pCore_two_quotient_eq_bot
  have hZ1 := SLMult.center_eq_bot_of_quot_statedSL hm eZ hO2
  rw [← hker] at hZ1
  have hinj : Function.Injective ρb := (MonoidHom.ker_eq_bot_iff ρb).mp hZ1
  refine ⟨fun c hc => ?_, ⟨(MulEquiv.ofBijective ρb ⟨hinj, hρbs⟩).trans eK⟩⟩
  have h1 : ρb (QuotientGroup.mk ⟨c, hc.1⟩) = 1 := (hρ'1 ⟨c, hc.1⟩).mpr hc.2
  have h2 : (QuotientGroup.mk ⟨c, hc.1⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 :=
    hinj (h1.trans (map_one _).symm)
  exact coe_mem_pCoreOf ((QuotientGroup.eq_one_iff _).mp h2)

theorem nonempty_mulEquiv_of_map_eq {A B P : Type*} [Group A] [Group B] [Group P]
    {X : Subgroup A} {Y : Subgroup B} (φ : A →* B) (hφ : Function.Injective φ) (h : X.map φ = Y)
    (eY : ↥Y ≃* P) : Nonempty (↥X ≃* P) :=
  ⟨((Subgroup.equivMapOfInjective X φ hφ).trans (MulEquiv.subgroupCongr h)).trans eY⟩

theorem nonempty_pairSL_equiv :
    Nonempty (↥(pairSL (ZMod 2)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) :=
  ⟨((MonoidHom.ofInjective (SL3One.rho_injective (K := ZMod 2))).trans
      (MulEquiv.subgroupCongr SL3One.range_rho)).symm.trans
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2))⟩

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

theorem nonempty_autOn_L_equiv (hc : S.Coord θ e) :
    Nonempty (↥(autOn L (fsuV T I)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) := by
  have he : (autI S.hV L).map (congrHom e) = pairSL (ZMod 2) := by
    rw [congrArg (autI S.hV ·) S.hL]
    exact hc.he
  obtain ⟨e₂⟩ := nonempty_pairSL_equiv
  have h1 : Nonempty (↥(autI S.hV L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) :=
    nonempty_mulEquiv_of_map_eq (congrHom e) (congrHom_injective e) he e₂
  exact h1

theorem inf_centralizer_L_le
    (hc : S.Coord θ e) :
    L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 L := by
  obtain ⟨eL⟩ := nonempty_autOn_L_equiv hc
  have hZ := CFSG.Quasithin.H13.commutatorElement_mem_pCoreOf S.hyp.fsu.quasisimple
    S.L_le_normalizer_V
    S.pCoreOf_L_le (fun h => th_not_mem hc (h hc.mem))
  exact (quot_equiv_of_autOn S.L_le_normalizer_V S.hyp.fsu.quasisimple.1 (Or.inl rfl) eL
    S.pCoreOf_L_le hZ).1

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem oTwoUpper_le_oPrimeResidualOf :
    oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ≤ oPrimeResidualOf 3 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := C.conf.hc
  have hL₀H : oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ≤ H :=
    le_sup_left.trans C.conf.hLH
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨⟨hxL, hxV0⟩, hxo⟩
  have hxL₀ : x ∈ oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) :=
    mem_oTwoUpper_of_odd ⟨hxL, hxV0⟩ hxo
  obtain ⟨b, r, hr, hxr⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3 (by norm_num)
  set u := x ^ 3 ^ b with hudef
  have hu1 : u = 1 := by
    have huL : u ∈ L := L.pow_mem hxL _
    have huV0 : u ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
        Subgroup G) : Set G) := by
      have h1 := Subgroup.pow_mem _ hxV0 (3 ^ b)
      rwa [C.hVp] at h1
    have hur : u ^ r = 1 := by rw [hudef, ← pow_mul, ← hxr, pow_orderOf_eq_one]
    have huo : Odd (orderOf u) := Odd.of_dvd_nat hxo (orderOf_pow_dvd _)
    have huV : u ∈ Subgroup.centralizer (fsuV T I : Set G) := by
      by_contra hcon
      obtain ⟨m, hm⟩ := exists_pow_of_odd hc (S.L_le_fsuM huL) huV0 huo hcon
      have hθr : θ ^ r ∈ Subgroup.centralizer (fsuV T I : Set G) := by
        have hconj : ∀ k : ℕ, ∀ v ∈ fsuV T I, θ ^ k * v * (θ ^ k)⁻¹ = (u ^ m) ^ k * v *
            ((u ^ m) ^ k)⁻¹ := by
          intro k
          induction k with
          | zero => intro v _; simp
          | succ k ih =>
            intro v hv
            have huN : u ^ m ∈ Subgroup.normalizer (fsuV T I : Set G) :=
              Subgroup.pow_mem _ (S.hMN (S.L_le_fsuM huL)) m
            have h1 : (u ^ m) * v * (u ^ m)⁻¹ ∈ fsuV T I :=
              (Subgroup.mem_normalizer_iff.mp huN v).mp hv
            have h2 : θ * v * θ⁻¹ = (u ^ m) * v * (u ^ m)⁻¹ := by
              have h3 := Subgroup.mem_centralizer_iff.mp hm _ h1
              calc θ * v * θ⁻¹ = (θ * (u ^ m)⁻¹) * ((u ^ m) * v * (u ^ m)⁻¹) *
                    (θ * (u ^ m)⁻¹)⁻¹ := by group
                _ = ((u ^ m) * v * (u ^ m)⁻¹) * (θ * (u ^ m)⁻¹) * (θ * (u ^ m)⁻¹)⁻¹ := by
                    rw [h3]
                _ = (u ^ m) * v * (u ^ m)⁻¹ := by group
            have hθv : θ * v * θ⁻¹ ∈ fsuV T I := by rw [h2]; exact h1
            calc θ ^ (k + 1) * v * (θ ^ (k + 1))⁻¹ = θ ^ k * (θ * v * θ⁻¹) * (θ ^ k)⁻¹ := by
                  group
              _ = (u ^ m) ^ k * (θ * v * θ⁻¹) * ((u ^ m) ^ k)⁻¹ := ih _ hθv
              _ = (u ^ m) ^ (k + 1) * v * ((u ^ m) ^ (k + 1))⁻¹ := by rw [h2]; group
        refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
        have h1 := hconj r v hv
        rw [← pow_mul, mul_comm m r, pow_mul, hur, one_pow, one_mul, inv_one, mul_one] at h1
        calc v * θ ^ r = θ ^ r * v * (θ ^ r)⁻¹ * θ ^ r := by rw [h1]
          _ = θ ^ r * v := by group
      apply th_not_mem hc
      have h1 := Subgroup.mul_mem _ (th_mul_inv_pow_mem hc hr) (Subgroup.pow_mem _ hθr r)
      simpa using h1
    have huO : u ∈ pCoreOf 2 L := inf_centralizer_L_le hc ⟨huL, huV⟩
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨u, huO⟩
    have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf u ∣ Nat.gcd (2 ^ k) (orderOf u) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') dvd_rfl
    have h2 : Nat.gcd (2 ^ k) (orderOf u) = 1 :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr huo)
    rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  have hx3 : ∃ k : ℕ, orderOf x = 3 ^ k := by
    have h1 : orderOf x ∣ 3 ^ b := orderOf_dvd_of_pow_eq_one hu1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    exact ⟨k, hk⟩
  exact Subgroup.subset_closure ⟨hL₀H hxL₀, hx3⟩

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
