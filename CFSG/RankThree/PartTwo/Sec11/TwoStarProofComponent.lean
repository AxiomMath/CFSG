module

public import CFSG.RankThree.PartTwo.KFacts.K71Item119
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.KFacts.K72List
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonPSL2Partition
public import CFSG.RankThree.PartTwo.KFacts.KS116ProofFactZ
public import CFSG.RankThree.PartTwo.KFacts.KS116ProofTorus

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace TwoStarProof

section MulAut

variable {X : Type*} [Group X]

theorem mulAut_mul_conj_mul_inv (φ : MulAut X) (x : X) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem map_centralizer_singleton_eq {Y : Type*} [Group Y] (e : X ≃* Y) (s : X) :
    (Subgroup.centralizer ({s} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e s} : Set Y) := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hx]
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz]

theorem eq_one_of_mem_of_conj_odd {Q : Subgroup (MulAut X)} (hQ : IsPGroup 2 Q)
    {D : Subgroup X} [Finite D] (hD : Odd (Nat.card D)) {z : X} (hz : z ∈ D)
    (hzQ : MulAut.conj z ∈ Q) : MulAut.conj z = 1 := by
  obtain ⟨n, hn⟩ := hQ ⟨_, hzQ⟩
  have h2 : (MulAut.conj z) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hDz : z ^ Nat.card D = 1 := by
    have := congrArg Subtype.val (pow_card_eq_one' (G := D) (x := ⟨z, hz⟩))
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have hD' : (MulAut.conj z) ^ Nat.card D = 1 := by rw [← map_pow, hDz, map_one]
  have hcop : Nat.Coprime (2 ^ n) (Nat.card D) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hD)
  have h := pow_gcd_eq_one.2 ⟨h2, hD'⟩
  rwa [hcop, pow_one] at h

end MulAut

section Models

variable {F : Type} [Field F] [Finite F]

theorem center_projSL_eq_bot : Subgroup.center (projSL 2 F) = ⊥ :=
  CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv (Sec4.projSLEquivPSL F)
    (CFSG.GorensteinWalter.psl2_center_eq_bot F)

theorem center_eq_bot_of_projSL {X : Type*} [Group X] (e : X ≃* projSL 2 F) :
    Subgroup.center X = ⊥ :=
  CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e center_projSL_eq_bot

theorem conj_injective_of_center_eq_bot {X : Type*} [Group X] (h : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro a b hab
  have hc : b⁻¹ * a ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := congrArg (fun φ : MulAut X => φ g) hab
    simp only [MulAut.conj_apply] at hg
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [hg]
      _ = b⁻¹ * a * g := by group
  rw [h, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

end Models

theorem centralizer_isCyclic_card {f : ℕ} (hf : 2 ≤ f) {X : Type*} [Group X]
    (e : X ≃* projSL 2 (GaloisField 2 f)) {s : X} (hs1 : s ≠ 1) (hs3 : s ^ 3 = 1) :
    IsCyclic (Subgroup.centralizer ({s} : Set X)) ∧
      (Nat.card (Subgroup.centralizer ({s} : Set X)) = 2 ^ f - 1 ∨
        Nat.card (Subgroup.centralizer ({s} : Set X)) = 2 ^ f + 1) := by
  classical
  set K := GaloisField 2 f
  have : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = 2 ^ f := GaloisField.card 2 f (by omega)
  have hf4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set P := Matrix.ProjectiveSpecialLinearGroup (Fin 2) K
  set ε : X ≃* P := e.trans (Sec4.projSLEquivPSL K) with hε
  set x := ε s with hx
  have hx1 : x ≠ 1 := fun h => hs1 (ε.injective (h.trans (map_one ε).symm))
  have hx3 : x ^ 3 = 1 := by rw [hx, ← map_pow, hs3, map_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₂⟩ := (inferInstance : Nonempty (Sylow 2 P))
  obtain ⟨U, S, hU, hUc, hS, hSc, hpart⟩ :=
    CFSG.Glauberman.Dickson.huppert_II_8_5_a_psl2_cover (p := 2) (f := f) hK P₂
  have hodd : Nat.gcd (Nat.card K - 1) 2 = 1 := by
    rw [hK]
    have : Odd (2 ^ f - 1) := Nat.Even.sub_odd (by omega)
      (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    exact Nat.coprime_two_right.mpr this
  rw [hodd, Nat.div_one, hK] at hUc hSc
  obtain ⟨T, ⟨hxT, hT⟩, -⟩ := hpart x hx1
  have hTcyc : IsCyclic T ∧ (Nat.card T = 2 ^ f - 1 ∨ Nat.card T = 2 ^ f + 1) := by
    rcases hT with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exfalso
      have h2 : IsPGroup 2 ((P₂ : Subgroup P).map (MulAut.conj g).toMonoidHom) :=
        P₂.isPGroup'.map _
      obtain ⟨n, hn⟩ := h2 ⟨x, hxT⟩
      have hxn : x ^ 2 ^ n = 1 := by
        have := congrArg Subtype.val hn
        rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
      have hcop : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by norm_num)
      have h := pow_gcd_eq_one.2 ⟨hxn, hx3⟩
      rw [hcop, pow_one] at h
      exact hx1 h
    · refine ⟨?_, Or.inl ?_⟩
      · exact isCyclic_of_surjective (U.equivMapOfInjective _ (MulEquiv.injective _))
          (MulEquiv.surjective _)
      · rw [← hUc]
        exact (Nat.card_congr (U.equivMapOfInjective _ (MulEquiv.injective _)).toEquiv).symm
    · refine ⟨?_, Or.inr ?_⟩
      · exact isCyclic_of_surjective (S.equivMapOfInjective _ (MulEquiv.injective _))
          (MulEquiv.surjective _)
      · rw [← hSc]
        exact (Nat.card_congr (S.equivMapOfInjective _ (MulEquiv.injective _)).toEquiv).symm
  obtain ⟨hTc, hTcard⟩ := hTcyc
  have hTC : T ≤ Subgroup.centralizer ({x} : Set P) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := (hTc.commGroup).mul_comm (⟨t, ht⟩ : T) ⟨x, hxT⟩
    exact congrArg Subtype.val this
  set κ : Matrix.SpecialLinearGroup (Fin 2) K ≃* P :=
    (KFacts.KS116Proof.projSLEquiv K).trans (Sec4.projSLEquivPSL K) with hκ
  have hx₀ : κ.symm x ≠ 1 := fun h => hx1 (by rw [← κ.apply_symm_apply x, h, map_one])
  have hCle : Nat.card (Subgroup.centralizer ({x} : Set P)) ≤ 2 ^ f + 1 := by
    have h1 := KFacts.KS116Proof.card_centralizer_le hx₀
    have h2 := map_centralizer_singleton_eq κ (κ.symm x)
    rw [MulEquiv.apply_symm_apply] at h2
    rw [← h2, Subgroup.card_map_of_injective κ.injective]
    rw [← Nat.card_eq_fintype_card, hK] at h1
    exact h1
  have hCT : Subgroup.centralizer ({x} : Set P) = T := by
    refine (Subgroup.eq_of_le_of_card_ge hTC ?_).symm
    obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hTC
    have hpos : 0 < Nat.card (Subgroup.centralizer ({x} : Set P)) := Nat.card_pos
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j
      · rw [mul_zero] at hj
        omega
      · rw [mul_one] at hj
        omega
    · exfalso
      have h1 : Nat.card T * 2 ≤ Nat.card (Subgroup.centralizer ({x} : Set P)) := by
        rw [hj]
        exact Nat.mul_le_mul_left _ hj2
      rcases hTcard with h | h <;> rw [h] at h1 <;> omega
  have hmap := map_centralizer_singleton_eq ε s
  rw [← hx, hCT] at hmap
  set ι := (Subgroup.centralizer ({s} : Set X)).equivMapOfInjective ε.toMonoidHom ε.injective
  have hcard : Nat.card (Subgroup.centralizer ({s} : Set X)) = Nat.card T := by
    rw [← hmap]
    exact Nat.card_congr ι.toEquiv
  refine ⟨?_, hcard ▸ hTcard⟩
  have : IsCyclic ((Subgroup.centralizer ({s} : Set X)).map ε.toMonoidHom) := hmap ▸ hTc
  exact isCyclic_of_surjective (hH := this) ι.symm ι.symm.surjective

theorem twoStar_component_L2Field {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (e : X ≃* projSL 2 (GaloisField 2 (3 * m))) {y : MulAut X} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    {Q : Subgroup (MulAut X)} (hQ : IsPGroup 2 Q) (hQy : ∀ φ ∈ Q, φ * y = y * φ)
    (hQn : ∀ x : X, y x = x → ∀ φ ∈ Q, MulAut.conj x * φ * (MulAut.conj x)⁻¹ ∈ Q) :
    Q = ⊥ := by
  have : Finite X := Finite.of_equiv _ (e.trans (Sec4.projSLEquivPSL _)).symm.toEquiv
  have hZ : Subgroup.center X = ⊥ := center_eq_bot_of_projSL e
  have hinj := conj_injective_of_center_eq_bot hZ
  have hkey : ∀ φ ∈ Q, ∀ x : X, y x = x → MulAut.conj (x * (φ x)⁻¹) ∈ Q := by
    intro φ hφ x hx
    have h1 := Q.mul_mem (hQn x hx φ hφ) (Q.inv_mem hφ)
    have e1 : MulAut.conj x * φ * (MulAut.conj x)⁻¹ * φ⁻¹ = MulAut.conj (x * (φ x)⁻¹) := by
      rw [map_mul, map_inv, ← mulAut_mul_conj_mul_inv φ x]
      group
    rwa [e1] at h1
  have hfix : ∀ φ ∈ Q, ∀ x : X, y x = x → y (φ x) = φ x := by
    intro φ hφ x hx
    have := congrArg (fun ψ : MulAut X => ψ x) (hQy φ hφ)
    simp only [MulAut.mul_apply, hx] at this
    exact this.symm
  by_cases hin : KFacts.IsInnerAut y
  ·
    obtain ⟨s, rfl⟩ := hin
    have hs1 : s ≠ 1 := by
      rintro rfl
      exact hy1 (map_one _)
    have hs3 : s ^ 3 = 1 := hinj (by rw [map_pow, hy3, map_one])
    obtain ⟨hDc, hDcard⟩ := centralizer_isCyclic_card (f := 3 * m) (by omega) e hs1 hs3
    set D := Subgroup.centralizer ({s} : Set X) with hD
    have hDodd : Odd (Nat.card D) := by
      have h4 : 4 ≤ 2 ^ (3 * m) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hev : Even (2 ^ (3 * m)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      rcases hDcard with h | h <;> rw [h]
      · exact Nat.Even.sub_odd (by omega) hev odd_one
      · exact hev.add_one
    have hmemD : ∀ x : X, MulAut.conj s x = x ↔ x ∈ D := by
      intro x
      rw [MulAut.conj_apply, hD, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        calc x * s = s * x * s⁻¹ * s := by rw [h]
          _ = s * x := by group
      · intro h
        rw [← h]
        group
    have hφD : ∀ φ ∈ Q, ∀ x ∈ D, φ x = x := by
      intro φ hφ x hx
      have hxfix : MulAut.conj s x = x := (hmemD x).mpr hx
      have hφx : φ x ∈ D := (hmemD _).mp (hfix φ hφ x hxfix)
      have hz : x * (φ x)⁻¹ ∈ D := D.mul_mem hx (D.inv_mem hφx)
      have h1 := eq_one_of_mem_of_conj_odd hQ hDodd hz (hkey φ hφ x hxfix)
      have h2 : x * (φ x)⁻¹ = 1 := hinj (by rw [h1, map_one])
      exact (mul_inv_eq_one.mp h2).symm
    rw [eq_bot_iff]
    intro φ hφ
    set φ' := MulAut.congr e φ with hφ'
    set ι := D.equivMapOfInjective e.toMonoidHom e.injective with hι
    have hT'c : IsCyclic (D.map e.toMonoidHom) :=
      isCyclic_of_surjective ι (MulEquiv.surjective _)
    have hT'card : Nat.card (D.map e.toMonoidHom) = Nat.card D :=
      (Nat.card_congr ι.toEquiv).symm
    have hφ'T : ∀ t ∈ D.map e.toMonoidHom, φ' t = t := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hφ', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply, MulEquiv.trans_apply, hφD φ hφ x hx]
    obtain ⟨t, htT, ht⟩ := KFacts.torusSelfCentralizingL2 (3 * m) (by omega)
      (D.map e.toMonoidHom) hT'c (hT'card ▸ hDcard) φ' hφ'T
    obtain ⟨d₀, hd₀, rfl⟩ := htT
    have hφconj : φ = MulAut.conj d₀ := by
      ext x
      have h1 := ht (e x)
      rw [hφ', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulEquiv.trans_apply] at h1
      apply e.injective
      rw [h1, MulAut.conj_apply, MulEquiv.coe_toMonoidHom, map_mul, map_mul, map_inv]
    rw [Subgroup.mem_bot, hφconj]
    exact eq_one_of_mem_of_conj_odd hQ hDodd hd₀ (hφconj ▸ hφ)
  ·
    set S := y.toMonoidHom.eqLocus (MonoidHom.id X) with hS
    obtain ⟨ι⟩ := KFacts.nonempty_eqLocus_mulEquiv_projSL_two (p := 2) (m := m) (by omega) e
      hy3 hin
    have hK4 : 4 ≤ Nat.card (GaloisField 2 m) := by
      rw [GaloisField.card 2 m (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK4
    have hSsimple : IsSimpleGroup S := MulEquiv.isSimpleGroup (ι.trans (Sec4.projSLEquivPSL _))
    have h3S : 3 ∣ Nat.card S := by
      rw [Nat.card_congr (ι.trans (Sec4.projSLEquivPSL _)).toEquiv]
      exact KFacts.three_dvd_card_psl2 _
    have hmemS : ∀ x : X, x ∈ S ↔ y x = x := fun x => Iff.rfl
    set N₀ : Subgroup S := (Q.comap (MulAut.conj : X →* MulAut X)).subgroupOf S with hN₀
    have hN₀n : N₀.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : MulAut.conj (n : X) ∈ Q := Subgroup.mem_subgroupOf.mp hn
      change MulAut.conj ((g : X) * n * (g : X)⁻¹) ∈ Q
      rw [map_mul, map_mul, map_inv]
      exact hQn g ((hmemS g).mp g.2) _ hn'
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N₀ with hb | ht
    ·
      have hφS : ∀ φ ∈ Q, ∀ x ∈ S, φ x = x := by
        intro φ hφ x hx
        have hφx : φ x ∈ S := (hmemS _).mpr (hfix φ hφ x hx)
        have hz : x * (φ x)⁻¹ ∈ S := S.mul_mem hx (S.inv_mem hφx)
        have hzN : (⟨x * (φ x)⁻¹, hz⟩ : S) ∈ N₀ :=
          Subgroup.mem_subgroupOf.mpr (hkey φ hφ x hx)
        rw [hb, Subgroup.mem_bot] at hzN
        have h2 : x * (φ x)⁻¹ = 1 := congrArg Subtype.val hzN
        exact (mul_inv_eq_one.mp h2).symm
      have hfac := KFacts.factZL2Even m hm (S.map e.toMonoidHom)
        ⟨(S.equivMapOfInjective e.toMonoidHom e.injective).symm.trans ι⟩
      have hcongr := KFacts.KS116Proof.card_fixing_congr e (S : Set X)
      have himg : (⇑e '' (S : Set X)) = ((S.map e.toMonoidHom : Subgroup _) : Set _) := by
        ext z
        simp
      rw [himg] at hcongr
      let FS : Subgroup (MulAut X) :=
        { carrier := {ψ | ∀ x ∈ S, ψ x = x}
          mul_mem' := fun {ψ₁ ψ₂} h₁ h₂ x hx => by
            rw [MulAut.mul_apply, h₂ x hx, h₁ x hx]
          one_mem' := fun x _ => rfl
          inv_mem' := fun {ψ} h x hx => by
            rw [← h x hx, MulAut.inv_apply_self, h x hx] }
      have hFS : Nat.card FS = 3 := hcongr.trans hfac
      have hQFS : Q ≤ FS := fun φ hφ x hx => hφS φ hφ x hx
      have hdvd := Subgroup.card_dvd_of_le hQFS
      rw [hFS] at hdvd
      obtain ⟨k, hk⟩ := hQ.exists_card_eq
      rw [hk] at hdvd
      have hk0 : k = 0 := by
        by_contra hk0
        have h2 : 2 ∣ 3 := (dvd_pow_self 2 hk0).trans hdvd
        omega
      rw [hk0, pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq Q hk
    ·
      exfalso
      have hSQ : ∀ z : S, MulAut.conj (z : X) ∈ Q := fun z =>
        Subgroup.mem_subgroupOf.mp (ht ▸ Subgroup.mem_top z)
      let f : S →* Q := ((MulAut.conj : X →* MulAut X).comp S.subtype).codRestrict Q hSQ
      have hf : Function.Injective f := fun a b hab =>
        Subtype.ext (hinj (congrArg Subtype.val hab))
      have hdvd : Nat.card S ∣ Nat.card Q := by
        rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
        exact Subgroup.card_subgroup_dvd_card _
      obtain ⟨k, hk⟩ := hQ.exists_card_eq
      rw [hk] at hdvd
      have h3 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h3S.trans hdvd))
      omega

end TwoStarProof

end CFSG.RankThree.PartTwo.Sec11
