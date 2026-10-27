module

public import CFSG.RankThree.PartTwo.Sec14.Item148ONLocProofMax
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.PartTwo.Sec14.Item148Res7ProofSig

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.GroupTheory

@[expose] def KF148SigONMax : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (A L K : Subgroup Γ) (e : Γ), Sig148 A L K e →
    Sec4.IsTripleCover (↥L ⧸ aschbacherSolvableCore 3 ↥L) CFSG.Blueprint.NativeSporadic.ON →
    IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    (∀ x : Γ, x ^ 3 = 1 → (∀ a ∈ A, a * x = x * a) → x ∈ A) →
    Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 7)) ∨
      (∃ _ : Fact (Nat.Prime 7), Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))

@[expose] def KF148SigONE27 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
    Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON →
    ∀ P H : Subgroup X, Late.IsE27 P → P ≤ Subgroup.normalizer (H : Set X) →
      Group.IsPerfect ↥H → IsQuasisimple (↥H ⧸ aschbacherSolvableCore 3 ↥H) →
      H ≤ ⨆ (p : X) (_ : p ∈ P) (_ : p ∉ Subgroup.center X),
        pPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({p} : Set X)) →
      ∃ _ : Fact (Nat.Prime 7), Nonempty (↥H ⧸ aschbacherSolvableCore 3 ↥H ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))

namespace ONLoc

theorem nonempty_thetaQuot_equiv {G H : Type*} [Group G] [Finite G] [Group H] (φ : G →* H)
    (hφ : Function.Surjective φ) (hs : Group.IsSolvable φ.ker) (h3 : ¬ 3 ∣ Nat.card φ.ker) :
    Nonempty (H ⧸ aschbacherSolvableCore 3 H ≃* G ⧸ aschbacherSolvableCore 3 G) := by
  obtain ⟨hNθ, hmap, -, -⟩ :=
    solvable_prime_complement_core_quotient_centralizers Nat.prime_three φ.ker hs h3
  set e := QuotientGroup.quotientKerEquivOfSurjective φ hφ with hedef
  have hθH : (aschbacherSolvableCore 3 (G ⧸ φ.ker)).map e.toMonoidHom =
      aschbacherSolvableCore 3 H :=
    CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  set e₂ := QuotientGroup.congr _ _ e hθH
  set e₃ := QuotientGroup.quotientMulEquivOfEq hmap.symm
  set e₄ := QuotientGroup.quotientQuotientEquivQuotient φ.ker (aschbacherSolvableCore 3 G) hNθ
  exact ⟨e₂.symm.trans (e₃.trans e₄)⟩

end ONLoc

theorem ONLoc.exists_e27_data
    {Γ : Type} [Group Γ] [Finite Γ] {A L K : Subgroup Γ} {e : Γ} (hS : Sig148 A L K e)
    (hON3 : Sec4.IsTripleCover (↥L ⧸ aschbacherSolvableCore 3 ↥L)
      CFSG.Blueprint.NativeSporadic.ON)
    (hLq : IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hmax : ∀ x : Γ, x ^ 3 = 1 → (∀ a ∈ A, a * x = x * a) → x ∈ A) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (P H : Subgroup X), Group.IsPerfect X ∧
      Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON ∧ Late.IsE27 P ∧
      P ≤ Subgroup.normalizer (H : Set X) ∧ Group.IsPerfect ↥H ∧
      IsQuasisimple (↥H ⧸ aschbacherSolvableCore 3 ↥H) ∧
      H ≤ ⨆ (p : X) (_ : p ∈ P) (_ : p ∉ Subgroup.center X),
        pPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({p} : Set X)) ∧
      Nonempty (↥H ⧸ aschbacherSolvableCore 3 ↥H ≃* ↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAL : A ≤ L := ONLoc.le_of_forall_mem hS.isE27 hS.mem hS.ne_one hS.le_centralizer
    hS.le_normalizer_L hLq hON3 hmax
  set X := ↥L ⧸ aschbacherSolvableCore 3 ↥L with hXdef
  set θL : Subgroup Γ := inSubgroup (aschbacherSolvableCore 3) L with hθLdef
  have hAθ : A ⊓ θL = ⊥ := ONLoc.inf_theta_eq_bot hS.isE27.isPGroup
  set ρ : ↥L →* X := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hρdef
  have hρ1 : ∀ y : ↥L, ρ y = 1 ↔ (y : Γ) ∈ θL := by
    intro y
    rw [hρdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨y, h, rfl⟩
    · rintro ⟨y', hy', hyy'⟩
      have : y' = y := Subtype.ext hyy'
      rw [← this]
      exact hy'
  have hρA : ∀ a : ↥L, (a : Γ) ∈ A → ρ a = 1 → (a : Γ) = 1 := by
    intro a ha h1
    have h2 : (a : Γ) ∈ A ⊓ θL := ⟨ha, (hρ1 a).mp h1⟩
    rw [hAθ] at h2
    exact h2
  set Abar : Subgroup X := (A.subgroupOf L).map ρ with hAbardef
  have hAbar27 : Nat.card Abar = 27 := by
    have hinj : Function.Injective (ρ.domRestrict (A.subgroupOf L)) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro a ha
      rw [Subgroup.mem_bot]
      have h1 := hρA a (Subgroup.mem_subgroupOf.mp a.2) ha
      exact Subtype.ext (Subtype.ext h1)
    rw [hAbardef, ← MonoidHom.domRestrict_range]
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hS.isE27.2]
  have hAbarE : Late.IsE27 Abar := by
    refine ⟨⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, ?_⟩, hAbar27⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := u
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := v
      change ρ x * ρ y = ρ y * ρ x
      have hc : (x : Γ) * y = y * x :=
        congrArg Subtype.val (hS.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hc
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (hS.isE27.1.2 _ (Subgroup.mem_subgroupOf.mp hx))
      rw [this, map_one]
  have heL : e ∈ L := hAL hS.mem
  have heZ : ρ ⟨e, heL⟩ ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) q
    rw [← hρdef, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hS.le_centralizer y.2))
  have he1 : ρ ⟨e, heL⟩ ≠ 1 := fun h => hS.ne_one (hρA _ hS.mem h)
  have hxZ : ∀ (x : Γ) (hxL : x ∈ L), x ∈ A → x ∉ Subgroup.zpowers e →
      ρ ⟨x, hxL⟩ ∉ Subgroup.center X := by
    intro x hxL hxA hxe hxZ
    have htop := zpowers_eq_top_of_prime_card (G := Subgroup.center X) hON3.1
      (g := ⟨_, heZ⟩) (fun h => he1 (congrArg Subtype.val h))
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (htop ▸ Subgroup.mem_top (⟨_, hxZ⟩ : Subgroup.center X))
    have h1 : ρ ⟨e, heL⟩ ^ n = ρ ⟨x, hxL⟩ := by
      have := congrArg Subtype.val hn
      simpa using this
    have h2 : ρ (⟨e, heL⟩ ^ n * (⟨x, hxL⟩ : ↥L)⁻¹) = 1 := by
      rw [map_mul, map_zpow, h1, map_inv, mul_inv_cancel]
    have h3 := hρA _ (by
      show e ^ n * x⁻¹ ∈ A
      exact A.mul_mem (zpow_mem hS.mem n) (A.inv_mem hxA)) h2
    have h4 : x = e ^ n := by
      have h5 : e ^ n * x⁻¹ = 1 := by simpa using h3
      rw [mul_inv_eq_one] at h5
      exact h5.symm
    exact hxe (h4 ▸ Subgroup.zpow_mem_zpowers e n)
  set f : ↥K →* X := ρ.comp (Subgroup.inclusion hS.le) with hfdef
  set Kbar : Subgroup X := f.range with hKbardef
  have hfθ : ∀ k : ↥K, f k = 1 ↔ (k : Γ) ∈ θL := fun k => hρ1 _
  have hKbarp : Group.IsPerfect ↥Kbar := by
    have : Group.IsPerfect ↥K := hS.isPerfect
    exact Group.IsPerfect.range f
  have hkerθ : ∀ k : ↥f.rangeRestrict.ker,
      Subgroup.inclusion hS.le (k : ↥K) ∈ aschbacherSolvableCore 3 ↥L := by
    intro k
    have h2 : f.rangeRestrict (k : ↥K) = 1 := k.2
    have h1 : f (k : ↥K) = 1 := by simpa using congrArg Subtype.val h2
    have h3 : ρ (Subgroup.inclusion hS.le (k : ↥K)) = 1 := h1
    exact (QuotientGroup.eq_one_iff _).mp h3
  let ι : ↥f.rangeRestrict.ker →* ↥(aschbacherSolvableCore 3 ↥L) :=
    { toFun := fun k => ⟨Subgroup.inclusion hS.le (k : ↥K), hkerθ k⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro a b hab
    have h1 := congrArg (fun t : ↥(aschbacherSolvableCore 3 ↥L) => ((t : ↥L) : Γ)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hker_s : Group.IsSolvable f.rangeRestrict.ker := by
    have : Group.IsSolvable ↥(aschbacherSolvableCore 3 ↥L) :=
      (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
    exact Group.isSolvable_of_isSolvable_injective hι
  have hker_3 : ¬ 3 ∣ Nat.card f.rangeRestrict.ker := by
    intro h3
    have hθ3 : ¬ 3 ∣ Nat.card ↥(aschbacherSolvableCore 3 ↥L) :=
      (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
    exact hθ3 (h3.trans (Subgroup.card_dvd_of_injective ι hι))
  obtain ⟨ψθ⟩ := ONLoc.nonempty_thetaQuot_equiv f.rangeRestrict f.rangeRestrict_surjective
    hker_s hker_3
  have hKbarq : IsQuasisimple (↥Kbar ⧸ aschbacherSolvableCore 3 ↥Kbar) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ψθ.symm hS.isQuasisimple
  have hAN : Abar ≤ Subgroup.normalizer (Kbar : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    have haA : (a : Γ) ∈ A := Subgroup.mem_subgroupOf.mp ha
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨k, rfl⟩ := hn
    have hk : (a : Γ) * k * (a : Γ)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hS.le_normalizer_K haA) k).mp k.2
    refine ⟨⟨_, hk⟩, ?_⟩
    have e1 : (Subgroup.inclusion hS.le ⟨_, hk⟩ : ↥L) = a * Subgroup.inclusion hS.le k * a⁻¹ :=
      Subtype.ext rfl
    show ρ (Subgroup.inclusion hS.le ⟨_, hk⟩) = ρ a * ρ (Subgroup.inclusion hS.le k) * (ρ a)⁻¹
    rw [e1, map_mul, map_mul, map_inv]
  have hXperf : Group.IsPerfect X := hLq.1
  have hgen : Kbar ≤ ⨆ (p : X) (_ : p ∈ Abar) (_ : p ∉ Subgroup.center X),
      pPrimeCoreOf 3 (Kbar ⊓ Subgroup.centralizer ({p} : Set X)) := by
    set J := ⨆ (p : X) (_ : p ∈ Abar) (_ : p ∉ Subgroup.center X),
      pPrimeCoreOf 3 (Kbar ⊓ Subgroup.centralizer ({p} : Set X)) with hJdef
    set J' : Subgroup Γ := (J.comap f).map K.subtype with hJ'def
    have hcore : ∀ x ∈ A, x ∉ Subgroup.zpowers e →
        pPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ)) ≤ J' := by
      intro x hxA hxe
      have hxL : x ∈ L := hAL hxA
      set V := pPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ)) with hVdef
      have hVK : V ≤ K := (pPrimeCoreOf_le 3 _).trans inf_le_left
      set xbar : X := ρ ⟨x, hxL⟩ with hxbardef
      set Vbar : Subgroup X := (V.subgroupOf K).map f with hVbardef
      have hVbar : Vbar ≤ pPrimeCoreOf 3 (Kbar ⊓ Subgroup.centralizer ({xbar} : Set X)) := by
        refine le_pPrimeCoreOf ?_ ?_ ?_
        ·
          rintro _ ⟨v, hv, rfl⟩
          refine Subgroup.mem_inf.mpr ⟨⟨v, rfl⟩, ?_⟩
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hvC : (v : Γ) * x = x * v := by
            have h1 := (pPrimeCoreOf_le 3 _ (Subgroup.mem_subgroupOf.mp hv)).2
            exact Subgroup.mem_centralizer_singleton_iff.mp h1
          rw [hfdef, MonoidHom.comp_apply, hxbardef, ← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext hvC
        ·
          intro y hy
          obtain ⟨⟨k, rfl⟩, hkC⟩ := Subgroup.mem_inf.mp hy
          rw [Subgroup.mem_centralizer_singleton_iff] at hkC
          set N₀ : Subgroup Γ := K ⊓ θL with hN₀def
          have hxK : x ∈ Subgroup.normalizer (K : Set Γ) := hS.le_normalizer_K hxA
          have hxθ : x ∈ Subgroup.normalizer (θL : Set Γ) :=
            SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore 3 L
              (hS.le_normalizer_L hxA)
          have hxN₀ : x ∈ Subgroup.normalizer (N₀ : Set Γ) :=
            Subgroup.inf_normalizer_le_normalizer_inf ⟨hxK, hxθ⟩
          have hkx : (k : Γ)⁻¹ * (x * k * x⁻¹) ∈ N₀ := by
            have hxk : x * (k : Γ) * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hxK k).mp k.2
            refine ⟨K.mul_mem (K.inv_mem k.2) hxk, ?_⟩
            have h1 : f k * xbar = xbar * f k := hkC
            have h2 : ρ ((⟨(k : Γ), hS.le k.2⟩ : ↥L)⁻¹ * (⟨x, hxL⟩ * ⟨(k : Γ), hS.le k.2⟩ *
                (⟨x, hxL⟩ : ↥L)⁻¹)) = 1 := by
              rw [map_mul, map_mul, map_mul, map_inv, map_inv]
              have e1 : ρ ⟨(k : Γ), hS.le k.2⟩ = f k := rfl
              rw [e1, ← hxbardef, ← h1]
              group
            exact (hρ1 _).mp h2
          have hpowk : ∀ j : ℕ, (k : Γ)⁻¹ * (x ^ j * k * (x ^ j)⁻¹) ∈ N₀ := by
            intro j
            induction j with
            | zero => simp
            | succ j ih =>
              have e2 : (k : Γ)⁻¹ * (x ^ (j + 1) * k * (x ^ (j + 1))⁻¹) =
                  (k : Γ)⁻¹ * (x * k * x⁻¹) * (x * ((k : Γ)⁻¹ * (x ^ j * k * (x ^ j)⁻¹)) * x⁻¹) :=
                by group
              rw [e2]
              exact N₀.mul_mem hkx ((Subgroup.mem_normalizer_iff.mp hxN₀ _).mp ih)
          have hN₀3 : ¬ 3 ∣ Nat.card N₀ := by
            intro h3
            have hθ3 : ¬ 3 ∣ Nat.card θL := by
              rw [hθLdef, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
              exact (solvable_prime_complement_core_characterization (H := ↥L)
                Nat.prime_three).2.2.1
            exact hθ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_right))
          have hx3 : x ^ 3 = 1 := hS.isE27.1.2 x hxA
          have hp : IsPGroup 3 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
            rw [Nat.card_zpowers, pow_one]
            have hx1 : x ≠ 1 := fun h => hxe (h ▸ Subgroup.one_mem _)
            exact orderOf_eq_prime hx3 hx1)
          set α : ↥(Subgroup.zpowers x) →* MulAut Γ :=
            MulAut.conj.comp (Subgroup.zpowers x).subtype with hαdef
          have hinv : ∀ (a : ↥(Subgroup.zpowers x)) (y : Γ), (k : Γ)⁻¹ * y ∈ N₀ →
              (k : Γ)⁻¹ * α a y ∈ N₀ := by
            intro a y hy
            obtain ⟨j, hj⟩ : ∃ j : ℕ, x ^ j = (a : Γ) :=
              Submonoid.mem_powers_iff _ _ |>.mp (mem_powers_iff_mem_zpowers.mpr a.2)
            have hαa : α a y = x ^ j * y * (x ^ j)⁻¹ := by
              rw [hαdef, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply, hj]
            rw [hαa]
            have e3 : (k : Γ)⁻¹ * (x ^ j * y * (x ^ j)⁻¹) = (k : Γ)⁻¹ * (x ^ j * k * (x ^ j)⁻¹) *
                (x ^ j * ((k : Γ)⁻¹ * y) * (x ^ j)⁻¹) := by group
            rw [e3]
            exact N₀.mul_mem (hpowk j)
              ((Subgroup.mem_normalizer_iff.mp (pow_mem hxN₀ j) _).mp hy)
          obtain ⟨c, hcN, hcfix⟩ :=
            (Semidihedral.Principal.coprime_invariant_coset_fixed 3 hp α N₀ hN₀3 k).2 hinv
          have hcK : c ∈ K := by
            have e4 : c = k * ((k : Γ)⁻¹ * c) := by group
            rw [e4]
            exact K.mul_mem k.2 hcN.1
          have hcx : c ∈ Subgroup.centralizer ({x} : Set Γ) := by
            rw [Subgroup.mem_centralizer_singleton_iff]
            have h1 := hcfix ⟨x, Subgroup.mem_zpowers x⟩
            rw [hαdef, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply] at h1
            calc c * x = x * c * x⁻¹ * x := by rw [h1]
              _ = x * c := by group
          have hfc : f ⟨c, hcK⟩ = f k := by
            have h1 : f ((k : ↥K)⁻¹ * ⟨c, hcK⟩) = 1 := (hfθ _).mpr hcN.2
            rw [map_mul, map_inv, inv_mul_eq_one] at h1
            exact h1.symm
          have hcV : c ∈ Subgroup.normalizer (V : Set Γ) :=
            le_normalizer_pPrimeCoreOf 3 _ ⟨hcK, hcx⟩
          rw [← hfc]
          refine Subgroup.mem_normalizer_fintype fun n hn => ?_
          obtain ⟨v, hv, rfl⟩ := hn
          have hvV : (v : Γ) ∈ V := Subgroup.mem_subgroupOf.mp hv
          have hcv : c * v * c⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hcV v).mp hvV
          refine ⟨⟨c * v * c⁻¹, hVK hcv⟩, Subgroup.mem_subgroupOf.mpr hcv, ?_⟩
          rw [← map_mul, ← map_inv, ← map_mul]
          rfl
        ·
          have h1 : Nat.card Vbar ∣ Nat.card (V.subgroupOf K) := Subgroup.card_map_dvd _ _
          have h2 : Nat.card (V.subgroupOf K) = Nat.card V :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv
          rw [h2] at h1
          exact Nat.Coprime.coprime_dvd_right h1 (coprime_card_pPrimeCoreOf 3 _)
      have hVJ : Vbar ≤ J := hVbar.trans (le_iSup₂_of_le xbar ⟨⟨x, hxL⟩,
        Subgroup.mem_subgroupOf.mpr hxA, rfl⟩ (le_iSup_of_le (hxZ x hxL hxA hxe) le_rfl))
      intro v hv
      refine ⟨⟨v, hVK hv⟩, ?_, rfl⟩
      exact hVJ ⟨⟨v, hVK hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
    have hKJ : K ≤ J' := hS.le_iSup.trans (iSup₂_le fun x hxA => iSup_le fun hxe =>
      hcore x hxA hxe)
    rintro _ ⟨k, rfl⟩
    obtain ⟨k', hk', hkk'⟩ := hKJ k.2
    have : k' = k := Subtype.ext hkk'
    rw [← this]
    exact hk'
  exact ⟨X, inferInstance, inferInstance, Abar, Kbar, hXperf, hON3, hAbarE, hAN, hKbarp, hKbarq,
    hgen, ⟨ψθ⟩⟩

theorem kf148SigONMax_of_e27
    (hE : KF148SigONE27) : KF148SigONMax := by
  intro Γ _ _ A L K e hS hON3 hLq hmax
  obtain ⟨X, _, _, P, H, hXp, hXT, hP, hPN, hHp, hHq, hgen, ⟨ψ⟩⟩ :=
    ONLoc.exists_e27_data hS hON3 hLq hmax
  obtain ⟨h7, ⟨φ⟩⟩ := hE X hXp hXT P H hP hPN hHp hHq hgen
  exact Or.inr ⟨h7, ⟨ψ.symm.trans φ⟩⟩

theorem step148KThetaONCover_of_sigMax (hKF : KF148SigONMax) : Step148KThetaONCover := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP c' L' hc' hc'B hL' hJ2 hd hON3
  have hLe : Le ∈ thetaComponentsAt 3 e := hP.2.2.2.2.2.2.2.2.1
  exact hKF G A Le K e (Res7Sig.sig148_of_isPoint148 h hYB hP) hON3
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt hLe)
    (fun x hx3 hxA => Sec4.mem_of_maximal_of_commute h.maximal_isElemAbelian hx3 hxA)

end CFSG.RankThree.PartTwo.Sec14
