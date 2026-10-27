module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL2Tools
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
import CFSG.RankThree.PartTwo.Sec6.Item64
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res7

open CFSG Matrix
open CFSG.GorensteinWalter (PSL2 PGL2 PGammaL2)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (pglAction semilinearAction
  semilinearEquivAut)
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Item434CharThree

theorem commute_of_mem_centralizer_psl2 {e : ℕ} (he : e ≠ 0) {x : PSL2 (GaloisField 3 e)}
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) {y z : PSL2 (GaloisField 3 e)}
    (hy : y ∈ Subgroup.centralizer ({x} : Set (PSL2 (GaloisField 3 e))))
    (hz : z ∈ Subgroup.centralizer ({x} : Set (PSL2 (GaloisField 3 e)))) : y * z = z * y := by
  set K := GaloisField 3 e with hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (PGL2 K) := finite_pgl2
  set π := ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K) with hπ
  have hπinj : Function.Injective π := ProjectiveSpecialLinearGroup.toPGL_injective
  set g := π x with hg
  have hg1 : g ≠ 1 := fun h => hx1 (hπinj (by rw [← hg, h, map_one]))
  have hg3 : g ^ 3 = 1 := by rw [hg, ← map_pow, hx3, map_one]
  have hP : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hg3 hg1, pow_one])
  obtain ⟨h, hh⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := unipPGL K)
    (by rw [card_unipPGL_galois he, factorization_card_pgl2 he]) hP
  have hgW : g ∈ (unipPGL K).map (MulAut.conj h).toMonoidHom := hh (Subgroup.mem_zpowers g)
  have hmem : ∀ w ∈ Subgroup.centralizer ({x} : Set (PSL2 K)),
      π w ∈ (unipPGL K).map (MulAut.conj h).toMonoidHom := by
    intro w hw
    apply mem_map_conj_unipPGL_of_commute hgW hg1
    rw [hg, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hw]
  apply hπinj
  rw [map_mul, map_mul]
  exact map_conj_unipPGL_commute (hmem y hy) (hmem z hz)

theorem mulAut_mul_conj_mul_inv {X : Type*} [Group X] (σ : MulAut X) (v : X) :
    σ * MulAut.conj v * σ⁻¹ = MulAut.conj (σ v) := by
  ext w
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem commute_of_fix_kleinFour
    {K : Type} [Field K] [Finite K]
    (hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K)) {V : Subgroup (PSL2 K)}
    (hV : CFSG.Assembly.IsElemAbelian 2 V) (hV4 : Nat.card V = 4) {α β : MulAut (PSL2 K)}
    (hα : ∀ v ∈ V, α v = v) (hβ : ∀ v ∈ V, β v = v) : α * β = β * α := by
  obtain ⟨p, n, hp, -, -, hKn⟩ := id hK
  have hcyc : IsCyclic (K ≃+* K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hKn).2
  set S := semilinearEquivAut K with hS
  set π := ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K) with hπ
  have hπinj : Function.Injective π := ProjectiveSpecialLinearGroup.toPGL_injective
  set C : Subgroup (PGammaL2 K) :=
    { carrier := {x | ∀ v ∈ V, S x v = v}
      mul_mem' := fun {a b} ha hb v hv => by rw [map_mul, MulAut.mul_apply, hb v hv, ha v hv]
      one_mem' := fun v _ => by rw [map_one, MulAut.one_apply]
      inv_mem' := fun {a} ha v hv => by
        have h1 := ha v hv
        rw [map_inv]
        calc (S a)⁻¹ v = (S a)⁻¹ (S a v) := by rw [h1]
          _ = v := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] } with hC
  have hmemC : ∀ x : PGammaL2 K, x ∈ C ↔ ∀ v ∈ V, S x v = v := fun x => Iff.rfl
  set V' := V.map π with hV'
  have hV'e : CFSG.Assembly.IsElemAbelian 2 V' := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a', ha', rfl⟩⟩ := a
      obtain ⟨_, ⟨b', hb', rfl⟩⟩ := b
      change π a' * π b' = π b' * π a'
      rw [← map_mul, ← map_mul]
      exact congrArg π (congrArg Subtype.val (hV.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
    · rintro _ ⟨a', ha', rfl⟩
      rw [← map_pow, hV.2 a' ha', map_one]
  have hV'4 : Nat.card V' = 4 := by rw [hV', Subgroup.card_map_of_injective hπinj, hV4]
  have : Finite (PGL2 K) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hV'K : IsKleinFour V' := isKleinFour_of_isElemAbelian hV'e hV'4
  have hcent : Subgroup.centralizer (V' : Set (PGL2 K)) = V' :=
    CFSG.GorensteinWalter.pgl2_kleinFour_centralizer_eq_self K hK V' hV'K
  set f : C →* (K ≃+* K) := SemidirectProduct.rightHom.comp C.subtype with hf
  have hker : f.ker ≤ Subgroup.center C := by
    intro x hx
    have hx1 : SemidirectProduct.rightHom (x : PGammaL2 K) = 1 := hx
    have hxr : (x : PGammaL2 K) ∈ (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).range := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      exact hx1
    obtain ⟨g, hgx⟩ := hxr
    have hSx : S x = pglAction K g := by
      rw [← hgx]
      exact CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inl K g
    have hgV : g ∈ V' := by
      rw [← hcent, Subgroup.mem_centralizer_iff]
      rintro _ ⟨v, hv, rfl⟩
      have h1 : pglAction K g v = v := by rw [← hSx]; exact (hmemC x).mp x.2 v hv
      have h2 := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.toPGL_pglAction K g v
      rw [h1] at h2
      change π v * g = g * π v
      calc π v * g = (g * π v * g⁻¹) * g := by rw [← h2]
        _ = g * π v := by group
    obtain ⟨v₀, hv₀, hv₀g⟩ := hgV
    have hSx' : S x = MulAut.conj v₀ := by
      rw [hSx, ← hv₀g]
      exact CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL K v₀
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply S.injective
    have hy : S y v₀ = v₀ := (hmemC y).mp y.2 v₀ hv₀
    have h3 := mulAut_mul_conj_mul_inv (S y) v₀
    rw [hy] at h3
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, hSx']
    calc S y * MulAut.conj v₀ = S y * MulAut.conj v₀ * (S y)⁻¹ * S y := by group
      _ = MulAut.conj v₀ * S y := by rw [h3]
  have hab := (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hker).is_comm.comm
  have hα' : S.symm α ∈ C := fun v hv => by rw [MulEquiv.apply_symm_apply]; exact hα v hv
  have hβ' : S.symm β ∈ C := fun v hv => by rw [MulEquiv.apply_symm_apply]; exact hβ v hv
  have h := congrArg (fun z : C => S (z : PGammaL2 K)) (hab ⟨_, hα'⟩ ⟨_, hβ'⟩)
  simpa only [Subgroup.coe_mul, map_mul, MulEquiv.apply_symm_apply] using h

theorem card_psl2_mul_two {F : Type} [Field F] [Finite F] (h2 : (-1 : F) ≠ 1) :
    Nat.card (PSL2 F) * 2 = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have h := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rwa [CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one h2]
    at h

theorem not_card_psl2_dvd {F : Type} [Field F] [Finite F] {m : ℕ} (hm : 2 < m)
    (hF : Nat.card F = 3 ^ m) (h2 : (-1 : F) ≠ 1) {N : ℕ}
    (hN : N = 9797760 ∨ N = 2694384000 ∨ N = 898128000 ∨ N = 6065280 ∨ N = 3265920) :
    ¬ Nat.card (PSL2 F) ∣ N := by
  intro hdvd
  have hP := card_psl2_mul_two h2
  rw [hF] at hP
  have hN0 : N ≤ 2694384000 := by omega
  have hNpos : 0 < N := by omega
  have hle : Nat.card (PSL2 F) ≤ 2694384000 := (Nat.le_of_dvd hNpos hdvd).trans hN0
  have hm7 : m ≤ 6 := by
    by_contra hm7
    push Not at hm7
    have h3m : 3 ^ 7 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm7
    have hq2 : (3 ^ 7) ^ 2 ≤ (3 ^ m) ^ 2 := Nat.pow_le_pow_left h3m 2
    have hmul : 3 ^ 7 * ((3 ^ 7) ^ 2 - 1) ≤ 3 ^ m * ((3 ^ m) ^ 2 - 1) :=
      Nat.mul_le_mul h3m (Nat.sub_le_sub_right hq2 1)
    norm_num at hmul
    omega
  interval_cases m
  · have hPc : Nat.card (PSL2 F) = 9828 := by norm_num at hP; omega
    rw [hPc] at hdvd
    rcases hN with rfl | rfl | rfl | rfl | rfl <;> norm_num at hdvd
  · have hPc : Nat.card (PSL2 F) = 265680 := by norm_num at hP; omega
    rw [hPc] at hdvd
    rcases hN with rfl | rfl | rfl | rfl | rfl <;> norm_num at hdvd
  · have hPc : Nat.card (PSL2 F) = 7174332 := by norm_num at hP; omega
    rw [hPc] at hdvd
    rcases hN with rfl | rfl | rfl | rfl | rfl <;> norm_num at hdvd
  · have hPc : Nat.card (PSL2 F) = 193709880 := by norm_num at hP; omega
    rw [hPc] at hdvd
    rcases hN with rfl | rfl | rfl | rfl | rfl <;> norm_num at hdvd

end CFSG.RankThree.PartTwo.Sec6.Res611Res7
