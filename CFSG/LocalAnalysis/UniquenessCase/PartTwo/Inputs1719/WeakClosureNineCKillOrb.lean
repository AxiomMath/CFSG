module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCKillGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TC914.Kill

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW

variable {X : Type} [Group X]

@[expose] def orbJoin (Lb K : Subgroup X) : Subgroup X := ⨆ c : ↥K, conjSubgroup Lb (c : X)

theorem conj_le_orbJoin {Lb K : Subgroup X} {c : X} (hc : c ∈ K) :
    conjSubgroup Lb c ≤ orbJoin Lb K :=
  le_iSup (fun d : ↥K => conjSubgroup Lb (d : X)) ⟨c, hc⟩

theorem le_orbJoin (Lb K : Subgroup X) : Lb ≤ orbJoin Lb K := by
  simpa [conjSubgroup_one] using conj_le_orbJoin (Lb := Lb) K.one_mem

theorem le_normalizer_orbJoin {Lb K M : Subgroup X}
    (h : ∀ c ∈ K, M ≤ normalizer (conjSubgroup Lb c : Set X)) :
    M ≤ normalizer (orbJoin Lb K : Set X) :=
  le_normalizer_iSup fun d => h d d.2

theorem le_centralizer_orbJoin {Lb K M : Subgroup X}
    (h : ∀ c ∈ K, M ≤ centralizer (conjSubgroup Lb c : Set X)) :
    M ≤ centralizer (orbJoin Lb K : Set X) :=
  le_centralizer_iff.mp (iSup_le fun d => le_centralizer_iff.mp (h d d.2))

theorem orbJoin_le {Lb K M : Subgroup X} (hLM : Lb ≤ M) (hKM : K ≤ normalizer (M : Set X)) :
    orbJoin Lb K ≤ M := by
  refine iSup_le fun d => fun x hx => ?_
  have h1 : (d : X) * x * (d : X)⁻¹ ∈ M := hLM (mem_conjSubgroup_iff.mp hx)
  simpa [mul_assoc] using (mem_normalizer_iff.mp (hKM (inv_mem d.2)) _).mp h1

theorem le_normalizer_orbJoin_self (Lb K : Subgroup X) :
    K ≤ normalizer (orbJoin Lb K : Set X) := by
  refine NFW.le_normalizer_of_conj_mem fun s hs x hx => ?_
  have hle : (orbJoin Lb K).map (MulAut.conj s).toMonoidHom ≤ orbJoin Lb K := by
    rw [orbJoin, Subgroup.map_iSup]
    refine iSup_le fun d => ?_
    have he : (conjSubgroup Lb (d : X)).map (MulAut.conj s).toMonoidHom =
        conjSubgroup Lb ((d : X) * s⁻¹) := by
      rw [← conjSubgroup_conjSubgroup]
      unfold conjSubgroup
      rw [inv_inv]
    rw [he]
    exact conj_le_orbJoin (mul_mem d.2 (inv_mem hs))
  exact hle ⟨x, hx, rfl⟩

theorem orbJoin_le_base {Lb Tb K : Subgroup X} (hK : K ≤ Tb) : orbJoin Lb K ≤ tcBase Lb Tb :=
  iSup_le fun d => conj_le_tcBase (hK d.2)

variable [Finite X] {B : Type} [Group B] [Finite B] {Lb Tb : Subgroup X}
  {π : ↥(tcN1 Lb Tb) →* B} {Es : Subgroup B}
variable (c : TCBar Lb Tb π Es)
include c

omit [Finite X] [Finite B] in
theorem base_le_normalizer_orbJoin {K : Subgroup X} (hK : K ≤ Tb) :
    tcBase Lb Tb ≤ normalizer (orbJoin Lb K : Set X) :=
  le_normalizer_orbJoin fun _ hd => c.base_le_normalizer_conj (hK hd)

omit [Finite X] [Finite B] in
theorem orbJoin_le_normalizer_conj {K : Subgroup X} (hK : K ≤ Tb) {t : X} (ht : t ∈ Tb) :
    orbJoin Lb K ≤ normalizer (conjSubgroup Lb t : Set X) :=
  (orbJoin_le_base hK).trans (c.base_le_normalizer_conj ht)

omit [Finite X] [Finite B] in
theorem isPGroup_center_conj (t : X) :
    IsPGroup 3 ↥(conjSubgroup Lb t ⊓ centralizer (conjSubgroup Lb t : Set X)) := by
  have h : IsPGroup 3 ↥(Lb ⊓ centralizer (Lb : Set X)) := by
    rintro ⟨z, hzL, hzC⟩
    obtain ⟨k, hk⟩ := c.center3 ⟨⟨z, hzL⟩, mem_center_iff.mpr fun g =>
      Subtype.ext ((mem_centralizer_iff.mp hzC) g g.2)⟩
    refine ⟨k, Subtype.ext ?_⟩
    simpa using congrArg (fun w : ↥(center ↥Lb) => ((w : ↥Lb) : X)) hk
  rw [← E3.conjSubgroup_centralizer, ← E3.conjSubgroup_inf]
  exact E3.isPGroup_conjSubgroup h t

omit [Finite B] in
theorem isPGroup_center_orbJoin {K : Subgroup X} (hK : K ≤ Tb) :
    IsPGroup 3 ↥(orbJoin Lb K ⊓ centralizer (orbJoin Lb K : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact isPGroup_iSup_inf_centralizer (fun d : ↥K => conjSubgroup Lb (d : X))
    (fun d d' hne => c.comm d (hK d.2) d' (hK d'.2) hne) fun d => isPGroup_center_conj c d

omit [Finite B] in
theorem eq_bot_of_le_conj {K : Subgroup X} (t : X) (hKL : K ≤ conjSubgroup Lb t)
    (hn : conjSubgroup Lb t ≤ normalizer (K : Set X)) (hK : IsPGroup 2 ↥K) : K = ⊥ := by
  have h1 : conjSubgroup K t⁻¹ ≤ Lb := by
    have := E3.conjSubgroup_mono_left t⁻¹ hKL
    rwa [E3.conjSubgroup_conj_inv] at this
  have h2 : Lb ≤ normalizer (conjSubgroup K t⁻¹ : Set X) := by
    have := E3.conjSubgroup_mono_left t⁻¹ hn
    rwa [E3.conjSubgroup_conj_inv, E3.conjSubgroup_normalizer] at this
  have h := c.eq_bot_of_le_Lb h1 h2 (E3.isPGroup_conjSubgroup hK t⁻¹)
  calc K = conjSubgroup (conjSubgroup K t⁻¹) t := (E3.conjSubgroup_inv_conj K t).symm
    _ = ⊥ := by rw [h, E3.conjSubgroup_bot]

omit [Finite B] in
theorem le_centralizer_conj {K : Subgroup X} (t : X)
    (hKN : K ≤ normalizer (conjSubgroup Lb t : Set X))
    (hn : conjSubgroup Lb t ≤ normalizer (K : Set X)) (hK : IsPGroup 2 ↥K) :
    K ≤ centralizer (conjSubgroup Lb t : Set X) := by
  have hbot : K ⊓ conjSubgroup Lb t = ⊥ := eq_bot_of_le_conj c t inf_le_right
    (fun l hl => mem_normalizer_inf (hn hl) (le_normalizer hl)) (hK.to_le inf_le_left)
  intro k hk
  rw [mem_centralizer_iff]
  intro l hl
  have hmem : k * l * k⁻¹ * l⁻¹ ∈ K ⊓ conjSubgroup Lb t := by
    refine mem_inf.mpr ⟨?_, mul_mem ((mem_normalizer_iff.mp (hKN hk) l).mp hl) (inv_mem hl)⟩
    have h1 : l * k⁻¹ * l⁻¹ ∈ K := (mem_normalizer_iff.mp (hn hl) k⁻¹).mp (inv_mem hk)
    simpa [mul_assoc] using mul_mem hk h1
  rw [hbot, mem_bot] at hmem
  calc l * k = (k * l * k⁻¹ * l⁻¹)⁻¹ * (k * l) := by group
    _ = k * l := by rw [hmem, inv_one, one_mul]

omit [Finite X] [Finite B] in
theorem T1_inf_centralizer_le_pCore :
    tcT1 Lb Tb ⊓ centralizer (Lb : Set X) ≤ pCoreOf 2 (tcN1 Lb Tb) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right)
    (sup_le ?_ ?_) (c.sylow.isPGroup.to_le (inf_le_left.trans inf_le_left))
  · intro l hl
    have hl' : l ∈ centralizer ((tcT1 Lb Tb ⊓ centralizer (Lb : Set X) : Subgroup X) : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz =>
        ((Subgroup.mem_centralizer_iff.mp hz.2) l hl).symm
    exact Subgroup.centralizer_le_normalizer _ hl'
  · exact fun t ht => mem_normalizer_inf (le_normalizer ht) (mem_normalizer_centralizer ht.2)

end CFSG.LocalAnalysis.WeakClosure81.TC914.Kill
