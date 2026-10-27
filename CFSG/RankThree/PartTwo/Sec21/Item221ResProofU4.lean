module

public import CFSG.RankThree.PartTwo.Sec21.Item221ProofZGenStatements
public import CFSG.RankThree.PartTwo.Sec21.Item223KFactsProofCore
import CFSG.RankThree.PartTwo.Sec21.Item221ProofZGen

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item221ResProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartOne.KFU (torusVec torusSU diagU symAct symAut symAut_apply blk)
open CFSG.LieType.Universal.Unitary (SUid SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution)

variable {G : Type} [Group G]

theorem nonempty_u4OddCtx [Finite G] {A Z : Subgroup G} {m : ℕ} (hm1 : 1 < m) (hmo : Odd m)
    (eZ : Z ≃* projSU 4 2 m) (hZ : Subgroup.center Z = ⊥) (hAe : IsElemAbelian 3 A)
    (hA81 : Nat.card A = 3 ^ 4) {z : G} (hzA : z ∈ A) (hzZ : z ∉ Z)
    (hZz : Z ≤ Subgroup.centralizer ({z} : Set G))
    (hAZ : Nat.card (A ⊓ Z : Subgroup G) = 3 ^ 3) :
    Nonempty (U4OddLines.U4OddCtx G Z A z m (GaloisField 2 (2 * m))) := by
  have hK : Nat.card (GaloisField 2 (2 * m)) = (2 ^ m) ^ 2 :=
    U4Lines.card_galoisField_two_mul m (by omega)
  have hU : UnitaryFieldData 2 m (GaloisField 2 (2 * m)) :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  set F : Subgroup Z := (A ⊓ Z).subgroupOf Z with hFdef
  have hFexp : ∀ x ∈ F, x ^ 3 = 1 := by
    intro x hx
    apply Subtype.ext
    have hxA : (x : G) ∈ A := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
    simpa using hAe.2 _ hxA
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    exact congrArg (fun t : A => (t : G)) (hAe.1.is_comm.comm
      ⟨x, (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1⟩
      ⟨y, (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).1⟩)
  have hFcard : Nat.card F = 3 ^ 3 := by
    rw [hFdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hAZ]
  obtain ⟨ψ, hψ⟩ := Item223KFactsProof.exists_diag_model (by omega) hmo eZ hZ F hFexp hFcomm
    hFcard
  exact ⟨{ hU := hU
           hf2 := by omega
           hpq := Item223KFactsProof.three_dvd_two_pow_add_one hmo
           hAe := hAe
           hA81 := hA81
           hcA := hzA
           hcL := hzZ
           hLc := hZz
           hAL := hAZ
           ψ := ψ
           hψ := fun g => by
             rw [← hψ g, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
             exact ⟨fun h => ⟨h, (ψ g).2⟩, fun h => h.1⟩ }⟩

theorem mem_starOf_of_kOf_le [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ : MulAut A} (hφ : φ ∈ dStar A)
    {Z : Subgroup G} (hKZ : kOf A φ ≤ Z) : φ ∈ starOf A Z := by
  obtain ⟨j, hjK, -, hj⟩ := exists_involution_kOf_wConj_eq h222 hpair hK hφ
  rw [← hj]
  exact Item233ZGenProof.wConj_mem_starOf j (hKZ hjK)

theorem exists_u4OddCtx [Finite G] {A : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hA81 : Nat.card A = 3 ^ 4) {φ : MulAut A} {Z : Subgroup G} (hKZ : kOf A φ ≤ Z)
    (hI : Item223OneInnerConcl A φ Z) :
    ∃ (m : ℕ) (z : G), 1 < m ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
      Nonempty (U4OddLines.U4OddCtx G Z A z m (GaloisField 2 (2 * m))) := by
  obtain ⟨m, hm1, hmo, ⟨eZ⟩, ⟨eK⟩, -, -, hAZ, hCZ⟩ := hI
  obtain ⟨x, y, hxy⟩ := exists_not_commute_of_mulEquiv_projSL eK
  have hZ : Subgroup.center Z = ⊥ :=
    Item223KFactsProof.center_eq_bot_of_mulEquiv_projSU (by omega) eZ
      (a := ⟨x, hKZ x.2⟩) (b := ⟨y, hKZ y.2⟩) fun h => hxy (Subtype.ext (by
        have := congrArg Subtype.val h
        simpa using this))
  have hC1 : (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hCZ
    omega
  obtain ⟨⟨z, hzC⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hC1
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hZz : Z ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hzC.2 w hw)
  have hzZ : z ∉ Z := by
    intro hz
    have hcen : (⟨z, hz⟩ : Z) ∈ Subgroup.center Z := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hzC.2 w w.2
    rw [hZ, Subgroup.mem_bot] at hcen
    exact hz1' (congrArg Subtype.val hcen)
  exact ⟨m, z, hm1, ⟨eK⟩,
    nonempty_u4OddCtx hm1 hmo eZ hZ hAe hA81 hzC.1 hzZ hZz hAZ⟩

namespace U4Z

variable [Finite G] {A Z : Subgroup G} {z : G} {m : ℕ}
  (C : U4OddLines.U4OddCtx G Z A z m (GaloisField 2 (2 * m)))

theorem actA_eq_wConj (π : Equiv.Perm (Fin 4)) : C.actA π = wConj A (C.permN π) := rfl

theorem permN_mem (π : Equiv.Perm (Fin 4)) :
    ((C.permN π : Subgroup.normalizer (A : Set G)) : G) ∈ Z :=
  C.phi_mem_L _

theorem exists_actA_swap_eq_conj {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ π : Equiv.Perm (Fin 4), C.actA (Equiv.swap a b) =
      wConj A (C.permN π) * C.actA (Equiv.swap c d) * (wConj A (C.permN π))⁻¹ := by
  obtain ⟨π, h1, h2⟩ := CFSG.RankThree.PartOne.KFU.exists_perm_pair hcd hab
  refine ⟨π, ?_⟩
  rw [← actA_eq_wConj, ← map_inv, ← map_mul, ← map_mul, ← Equiv.swap_apply_apply, h1, h2]

theorem exists_swap_of_isReflectionOn {ρ : MulAut A} (hρZ : ρ ∈ starOf A Z)
    (hρ : IsReflectionOn ρ) : ∃ a b : Fin 4, a ≠ b ∧ ρ = C.actA (Equiv.swap a b) := by
  have := C.hU.finite
  rw [C.starOf_eq_range] at hρZ
  obtain ⟨σ, rfl⟩ := hρZ
  obtain ⟨a, b, hab, rfl⟩ := (C.isReflectionOn_actA_iff σ).mp hρ
  exact ⟨a, b, hab, rfl⟩

end U4Z

theorem reflDStar_four [Finite G] (h222 : Item222) (hKW : KOfWellDefinedAll)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4)
    {φ : MulAut A} (hφ : φ ∈ dStar A) {Z : Subgroup G} (hKZ : kOf A φ ≤ Z)
    (hI : Item223OneInnerConcl A φ Z) :
    ∀ ρ ∈ starOf A Z, IsReflectionOn ρ → ρ ∈ dStar A := by
  intro ρ hρZ hρ
  have hK := hKW G A E U c L hpair
  obtain ⟨m, z, -, -, ⟨C⟩⟩ := exists_u4OddCtx hpair.mem_S.1.1 hA81 hKZ hI
  have hφZ := mem_starOf_of_kOf_le h222 hpair hK hφ hKZ
  obtain ⟨a, b, hab, rfl⟩ := U4Z.exists_swap_of_isReflectionOn C hρZ hρ
  obtain ⟨c', d, hcd, hφeq⟩ := U4Z.exists_swap_of_isReflectionOn C hφZ hφ.1
  obtain ⟨π, hπ⟩ := U4Z.exists_actA_swap_eq_conj C hab hcd
  rw [hπ, ← hφeq]
  exact conj_mem_dStar (C.permN π) hφ

namespace U4Z

variable [Finite G] {A Z : Subgroup G} {z : G} {m : ℕ}
  (C : U4OddLines.U4OddCtx G Z A z m (GaloisField 2 (2 * m)))

theorem theta_mem_fixedInG {a b : Fin 4} {d : torusVec 3 4 (GaloisField 2 (2 * m))}
    (hd : d ∈ Item223KFactsProof.hplane (GaloisField 2 (2 * m)) a b) :
    C.theta d ∈ fixedInG A (C.actA (Equiv.swap a b)) := by
  refine ⟨⟨C.theta d, C.theta_mem_A d⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_fixedSubgroupOf, C.actA_theta]
  have hfix : symAct 3 (GaloisField 2 (2 * m)) (Equiv.swap a b) d = d := by
    have h := (mem_fixedSubgroupOf _ d).mp hd
    rwa [symAut_apply] at h
  simp only [hfix]

@[expose] noncomputable def pre (H : Subgroup G) :
    Subgroup (GL (Fin 4) (GaloisField 2 (2 * m))) :=
  (H.comap C.phi).map (unitarySU 2 m (GaloisField 2 (2 * m)) 4).subtype

theorem pre_mono {H H' : Subgroup G} (h : H ≤ H') : pre C H ≤ pre C H' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem phi_mem_of_mem_pre {H : Subgroup G} {g : unitarySU 2 m (GaloisField 2 (2 * m)) 4}
    (hg : (g : GL (Fin 4) (GaloisField 2 (2 * m))) ∈ pre C H) : C.phi g ∈ H := by
  obtain ⟨u, hu, hug⟩ := hg
  have : u = g := Subtype.ext hug
  rw [← this]
  exact hu

theorem pre_eq_blk {a b : Fin 4} (hab : a ≠ b) {K' : Subgroup G} (hK'Z : K' ≤ Z)
    (hK'C : K' ≤ Subgroup.centralizer (fixedInG A (C.actA (Equiv.swap a b)) : Set G))
    (eK : K' ≃* projSL 2 (GaloisField 2 m)) : pre C K' = blk C.hU hab := by
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  have := C.hU.finite
  have hK'r : K' ≤ C.phi.range := by
    intro x hx
    exact ⟨C.ψ.symm ⟨x, hK'Z hx⟩, by rw [U4OddLines.U4OddCtx.coe_phi, MulEquiv.apply_symm_apply]⟩
  let e₁ : K'.comap C.phi ≃* K' :=
    (Subgroup.equivMapOfInjective (K'.comap C.phi) C.phi C.phi_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hK'r))
  let e₂ : K'.comap C.phi ≃* pre C K' :=
    Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)
  let e : pre C K' ≃* projSL 2 (GaloisField 2 m) := e₂.symm.trans (e₁.trans eK)
  have hm2 : 2 ≤ m := C.hf2
  have hSp := isPerfect_of_mulEquiv_projSL hm2 e
  have hc : ∀ g ∈ pre C K', ∀ d ∈ Item223KFactsProof.hplane (GaloisField 2 (2 * m)) a b,
      g * diagU (d : Fin 4 → (GaloisField 2 (2 * m))ˣ) =
        diagU (d : Fin 4 → (GaloisField 2 (2 * m))ˣ) * g := by
    rintro _ ⟨u, hu, rfl⟩ d hd
    have h1 : C.theta d * C.phi u = C.phi u * C.theta d :=
      Subgroup.mem_centralizer_iff.mp (hK'C hu) _ (theta_mem_fixedInG C hd)
    rw [U4OddLines.U4OddCtx.theta_apply, ← map_mul, ← map_mul] at h1
    have h2 := congrArg (fun x : unitarySU 2 m (GaloisField 2 (2 * m)) 4 =>
      (x : GL (Fin 4) (GaloisField 2 (2 * m)))) (C.phi_injective h1)
    simp only [Subgroup.coe_mul, U4OddLines.U4OddCtx.coe_torU] at h2
    exact h2.symm
  have hle := Item223KFactsProof.le_blk_of_perfect C.hU hζ hab (Subgroup.map_subtype_le _) hSp hc
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Item223KFactsProof.card_blk C.hU hab, Nat.card_congr e.toEquiv, card_projSL_two m (by omega)]

end U4Z

@[expose] noncomputable def adjBlk {m : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData 2 m K)
    (i : Fin 3) : Subgroup (GL (Fin 4) K) :=
  blk hU (Fin.castSucc_lt_succ (i := i)).ne

theorem unitarySU_le_iSup_adjBlk {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hU : UnitaryFieldData 2 m K) (hK : Nat.card K = (2 ^ m) ^ 2) (hm : 2 ≤ m) :
    unitarySU 2 m K 4 ≤ ⨆ i : Fin 3, adjBlk hU i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 2 ^ m ≠ 2 := by
    intro h
    have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have htop := CFSG.ClassicalInvolution.Phan.iSup_range_blockEmb2 (K := K) (p := 2) (f := m) hK hq 3
  have hSU : unitarySU 2 m K 4 = SUid (unitaryInvolution K 2 m) 4 :=
    (SUid_eq_statedSU hK 4).symm
  have hmap : (SUid (unitaryInvolution K 2 m) 4) =
      (⨆ i : Fin 3, (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 m 3 i).range).map
        (SUid (unitaryInvolution K 2 m) 4).subtype := by
    rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hSU, hmap, Subgroup.map_iSup]
  refine iSup_mono fun i => ?_
  rw [adjBlk, CFSG.RankThree.PartOne.KFU.blk_eq_map_blockEmb_adjacent hU (m := 4) (i := i)
    (by omega) (a := Fin.castSucc i) (b := Fin.succ i) rfl rfl]
  exact le_rfl

theorem rootGen_four [Finite G] (h222 : Item222) (hKW : KOfWellDefinedAll)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4)
    {φ : MulAut A} (hφ : φ ∈ dStar A) {Z : Subgroup G} (hKZ : kOf A φ ≤ Z)
    (hI : Item223OneInnerConcl A φ Z) :
    Z ≤ ⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z), kOf A ψ := by
  have hK := hKW G A E U c L hpair
  obtain ⟨m, z, hm1, ⟨eK⟩, ⟨C⟩⟩ := exists_u4OddCtx hpair.mem_S.1.1 hA81 hKZ hI
  have := C.hU.finite
  have hφZ := mem_starOf_of_kOf_le h222 hpair hK hφ hKZ
  obtain ⟨c', d, hcd, hφeq⟩ := U4Z.exists_swap_of_isReflectionOn C hφZ hφ.1
  set N := ⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z), kOf A ψ with hN
  have hblk : ∀ i : Fin 3, adjBlk C.hU i ≤ U4Z.pre C N := by
    intro i
    have hab : (Fin.castSucc i : Fin 4) ≠ Fin.succ i := (Fin.castSucc_lt_succ (i := i)).ne
    obtain ⟨π, hπ⟩ := U4Z.exists_actA_swap_eq_conj C hab hcd
    set w := C.permN π with hw
    set ψ := C.actA (Equiv.swap (Fin.castSucc i) (Fin.succ i)) with hψdef
    have hψφ : ψ = wConj A w * φ * (wConj A w)⁻¹ := by rw [hπ, ← hφeq]
    have hψD : ψ ∈ dStar A := hψφ ▸ conj_mem_dStar w hφ
    have hψZ : ψ ∈ starOf A Z := C.actA_mem_starOf _
    have hKψ : kOf A ψ = (kOf A φ).map (MulAut.conj (w : G)).toMonoidHom := by
      rw [hψφ]
      exact kOf_conj_of_unique hK w hφ
    have hwZ : (w : G) ∈ Z := U4Z.permN_mem C π
    have hKψZ : kOf A ψ ≤ Z := by
      rw [hKψ]
      rintro _ ⟨x, hx, rfl⟩
      exact Z.mul_mem (Z.mul_mem hwZ (hKZ hx)) (Z.inv_mem hwZ)
    have eKψ : kOf A ψ ≃* projSL 2 (GaloisField 2 m) := by
      rw [hKψ]
      exact ((kOf A φ).equivMapOfInjective _ (MulAut.conj (w : G)).injective).symm.trans eK
    have hKψC : kOf A ψ ≤ Subgroup.centralizer (fixedInG A ψ : Set G) :=
      (kOf_le_kZero hK hψD).trans (kZero_le_centralizer A ψ)
    rw [adjBlk, ← U4Z.pre_eq_blk C hab hKψZ hKψC eKψ]
    exact U4Z.pre_mono C (Item233ZGenProof.kOf_le_iSup hψD hψZ)
  have hgen : unitarySU 2 m (GaloisField 2 (2 * m)) 4 ≤ U4Z.pre C N :=
    (unitarySU_le_iSup_adjBlk C.hU (U4Lines.card_galoisField_two_mul m (by omega)) C.hf2).trans
      (iSup_le hblk)
  intro x hx
  set g := C.ψ.symm ⟨x, hx⟩ with hg
  have hgx : C.phi g = x := by rw [U4OddLines.U4OddCtx.coe_phi, hg, MulEquiv.apply_symm_apply]
  rw [← hgx]
  exact U4Z.phi_mem_of_mem_pre C (hgen g.2)

end CFSG.RankThree.PartTwo.Sec21.Item221ResProof
