module

public import CFSG.Quasithin.Background.FFC10A
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Quasithin.Background.SmithB51LnB42
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Background.SmithB42L2Base

public section

namespace CFSG.Quasithin

namespace B42L2

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped MatrixGroups

theorem card_fixed_le {K : Type} [Field K] [Finite K] (M : Matrix (Fin 2) (Fin 2) K)
    (hM : M ≠ 1) : Nat.card {v : Fin 2 → K // M.mulVec v = v} ≤ Nat.card K := by
  let N : Submodule K (Fin 2 → K) := LinearMap.ker (Matrix.mulVecLin (M - 1))
  have hN : ∀ v, v ∈ N ↔ M.mulVec v = v := fun v => by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
      sub_eq_zero]
  have hne : N ≠ ⊤ := by
    intro htop
    apply hM
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [Matrix.one_mulVec]
    exact (hN v).1 (by rw [htop]; trivial)
  have h1 : Module.finrank K N < Module.finrank K (Fin 2 → K) := Submodule.finrank_lt hne
  rw [Module.finrank_fin_fun] at h1
  have h2 : Nat.card N = Nat.card K ^ Module.finrank K N :=
    Module.natCard_eq_pow_finrank (K := K) (V := N)
  have h3 : Nat.card {v : Fin 2 → K // M.mulVec v = v} = Nat.card N :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => (hN v).symm)
  rw [h3, h2]
  calc Nat.card K ^ Module.finrank K N ≤ Nat.card K ^ 1 :=
        Nat.pow_le_pow_right Nat.card_pos (by omega)
    _ = Nat.card K := pow_one _

theorem card_le_of_isPGroup {M : Type*} [Group M] {L A : Subgroup M} (hAL : A ≤ L)
    (hA : IsPGroup 2 A) {n : ℕ} (hn : 1 ≤ n) (hL : Nat.card L = 2 ^ n * ((2 ^ n) ^ 2 - 1)) :
    Nat.card A ≤ 2 ^ n ∧ (Nat.card A = 2 ^ n → ¬ 2 ∣ (A.subgroupOf L).index) := by
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hodd : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := by
    rintro ⟨k, hk⟩
    have : 2 ∣ (2 ^ n) ^ 2 := ⟨2 ^ n * 2 ^ (n - 1), by
      rw [sq, mul_comm 2, mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]⟩
    obtain ⟨m, hm⟩ := this
    have hpos : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  have hLpos : Nat.card L ≠ 0 := by
    rw [hL]
    refine Nat.mul_ne_zero (by positivity) ?_
    have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    omega
  have : Finite L := Nat.finite_of_card_ne_zero hLpos
  have : Finite A := Finite.of_injective (Subgroup.inclusion hAL) (Subgroup.inclusion_injective hAL)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have h1 := Subgroup.card_mul_index (A.subgroupOf L)
  rw [show Nat.card (A.subgroupOf L) = Nat.card A from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hL, hk] at h1
  have hcop : Nat.Coprime (2 ^ k) ((2 ^ n) ^ 2 - 1) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have hdvd : 2 ^ k ∣ 2 ^ n := hcop.dvd_of_dvd_mul_right ⟨_, h1.symm⟩
  have hle : 2 ^ k ≤ 2 ^ n := Nat.le_of_dvd (by positivity) hdvd
  refine ⟨hk ▸ hle, fun heq => ?_⟩
  rw [hk] at heq
  rw [heq] at h1
  have hidx : (A.subgroupOf L).index = (2 ^ n) ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_left (by positivity) h1
  rw [hidx]
  exact hodd

variable {V : Type} [CommGroup V] [Finite V]

theorem case1_of_natural (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥) {n : ℕ} (hn : 1 ≤ n) {F : Type}
    [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n) (θL : ↥L ≃* SL(2, F))
    (e : V ≃* Multiplicative (Fin 2 → F))
    (he : ∀ (l : ↥L) (v : V), e ((l : MulAut V) v) = Multiplicative.ofAdd
      ((θL l : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (e v))))
    (hw : ∀ B, IsFFStarOffender G B → Nat.card B * Nat.card (fixV B) = Nat.card V)
    {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) : B42Case1 G L A := by
  classical
  have hcardF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  set Γ := StatedSL 2 F with hΓ
  let π : ↥Γ →* ↥L :=
    θL.symm.toMonoidHom.comp (specialLinearGroupEquivStatedSL 2 F).symm.toMonoidHom
  have hπ : Function.Surjective π :=
    θL.symm.surjective.comp (specialLinearGroupEquivStatedSL 2 F).symm.surjective
  have hπe : ∀ (γ : ↥Γ) (v : V), e (((π γ : ↥L) : MulAut V) v) = natAct Γ γ (e v) := by
    intro γ v
    obtain ⟨M, rfl⟩ := (specialLinearGroupEquivStatedSL 2 F).surjective γ
    rw [he]
    simp [π, natAct, specialLinearGroupEquivStatedSL_coe]
  have hReal : (FFModel.nat Γ).RealizesVia L ⊤ ⊥ π :=
    G64.realizesVia_nat_of hπ bot_le (fun _ _ _ => trivial) (fun h z hz => by
      rw [Subgroup.mem_bot] at hz ⊢
      rw [hz, map_one]) (e.toMonoidHom.comp (⊤ : Subgroup V).subtype)
      (fun x => ⟨⟨e.symm x, trivial⟩, by simp⟩)
      (fun u => by
        rw [Subgroup.mem_bot]
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
          MulEquivClass.map_eq_one_iff])
      (fun γ u _ => hπe γ u)
  have hLmap : L.map (H.congrHom e) = H.natImage Γ := H.map_congrHom_eq_natImage Γ hπ e hπe
  have hle : ∀ B, IsFFStarOffender G B → B ≤ L := by
    intro B hB
    have hEN : B.map (H.congrHom e) ≤ H.natNorm Γ := by
      have h1 := Subgroup.map_mono (f := H.congrHom e)
        (hB.1.trans (le_normalizer_of_b4Hyp hHyp))
      rwa [Subgroup.map_equiv_normalizer_eq L (MulAut.congr e), hLmap] at h1
    have hEl := (H.isElemAbelian2_map_congrHom e).2 hB.2.2.1
    have hoff : Nat.card (H.StdMod (Fin 2) F) ≤
        Nat.card (B.map (H.congrHom e)) * Nat.card (fixV (B.map (H.congrHom e))) := by
      rw [H.card_map_congrHom, H.fixV_map_congrHom,
        Subgroup.card_map_of_injective e.injective, ← Nat.card_congr e.toEquiv]
      exact card_le_of_offender hB
    have h2 := B69.le_natImage_of_offender hn hcardF hEN (fun x hx => hEl.2 x hx)
      (fun x hx y hy => hEl.1 x hx y hy) hoff
    rw [← hLmap] at h2
    exact (H.map_congrHom_le_iff e).1 h2
  have hAL : A ≤ L := hle A hA
  have hfix : Nat.card (fixV A) ≤ 2 ^ n := by
    obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.2.1
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    set M : Matrix (Fin 2) (Fin 2) F := (θL ⟨a, hAL haA⟩ : Matrix (Fin 2) (Fin 2) F) with hMdef
    have hM : M ≠ 1 := by
      intro h
      have h1 : θL ⟨a, hAL haA⟩ = 1 := Subtype.ext h
      have h2 : (⟨a, hAL haA⟩ : ↥L) = 1 := θL.injective (h1.trans (map_one θL).symm)
      exact ha1' (congrArg Subtype.val h2)
    let f : ↥(fixV A) → {x : Fin 2 → F // M.mulVec x = x} := fun v =>
      ⟨Multiplicative.toAdd (e v), by
        have h1 := he ⟨a, hAL haA⟩ v
        rw [show ((⟨a, hAL haA⟩ : ↥L) : MulAut V) (v : V) = v from v.2 a haA] at h1
        exact (congrArg Multiplicative.toAdd h1).symm⟩
    have hf : Function.Injective f := by
      intro v w hvw
      have h1 : e v = e w := Multiplicative.toAdd.injective (congrArg Subtype.val hvw)
      exact Subtype.ext (e.injective h1)
    calc Nat.card (fixV A) ≤ Nat.card {x : Fin 2 → F // M.mulVec x = x} :=
          Nat.card_le_card_of_injective f hf
      _ ≤ Nat.card F := card_fixed_le M hM
      _ = 2 ^ n := hcardF
  have hVc : Nat.card V = 2 ^ n * 2 ^ n := by
    rw [Nat.card_congr e.toEquiv]
    show Nat.card (Fin 2 → F) = _
    rw [Nat.card_fun, Nat.card_fin, hcardF, sq]
  have hLc : Nat.card L = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr θL.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      hcardF]
  obtain ⟨hAq, hidx⟩ := card_le_of_isPGroup hAL hA.2.2.1.isPGroup hn hLc
  have hAq' : Nat.card A = 2 ^ n := by
    refine le_antisymm hAq ?_
    by_contra hlt
    push Not at hlt
    have h1 := card_le_of_offender hA
    rw [hVc] at h1
    have h2 : Nat.card A * Nat.card (fixV A) < 2 ^ n * 2 ^ n :=
      calc Nat.card A * Nat.card (fixV A) ≤ Nat.card A * 2 ^ n := Nat.mul_le_mul_left _ hfix
        _ < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_pos_right hlt (by positivity)
    omega
  refine ⟨le_antisymm (iSup₂_le fun B hB => hle B hB) (B5.Ln.le_ffJ_of_center hHyp hZ hA),
    ⟨n, F, inferInstance, inferInstance, hcardF, π, hReal⟩,
    ⟨hAL, hA.2.2.1.isPGroup, hidx hAq'⟩, qOf_eq_one_of_weight hV hA hw⟩

end B42L2

end CFSG.Quasithin
