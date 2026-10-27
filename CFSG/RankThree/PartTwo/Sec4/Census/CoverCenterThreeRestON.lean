module

public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestPairing
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.Sporadic.ON.Simple
public import CFSG.Foundations.Basic
public import Certificates.Certificate8007
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.SectionRank.OpsSpec

open CFSG.Blueprint CFSG.SectionRank.Native LocalWitness

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem powProdIdx_spec : ∀ (xs : List M), (∀ X ∈ xs, Sp.WF X) → ∀ f : ℕ → ℕ,
    Sp.WF (O.powProdIdx xs f) ∧
      Sp.toMat (O.powProdIdx xs f) =
        (List.ofFn fun k : Fin xs.length => Sp.toMat xs[k] ^ f k).prod
  | [], _, _ => ⟨Sp.one_wf, by simp [Ops.powProdIdx, Sp.toMat_one]⟩
  | X :: xs, hxs, f => by
    have hX := hxs X List.mem_cons_self
    obtain ⟨w1, e1⟩ := Sp.pow_spec hX (f 0)
    obtain ⟨w2, e2⟩ := powProdIdx_spec xs (fun Y hY => hxs Y (List.mem_cons_of_mem _ hY))
      fun k => f (k + 1)
    refine ⟨Sp.mul_wf w1 w2, ?_⟩
    rw [Ops.powProdIdx, Sp.toMat_mul w1 w2, e1, e2, List.ofFn_succ, List.prod_cons]
    rfl

theorem norm_of_check [Inhabited M] (D : NormData) (h : O.normCheck D = true) :
    ∃ (x : Fin D.base.outs.length → (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ)
      (g : Fin D.gens.length → (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ),
      (∀ i, x i ^ 3 = 1) ∧ (∀ i j, x i * x j = x j * x i) ∧
      (∀ a : Fin D.base.outs.length → Fin 3, a ≠ 0 →
        (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ 1) ∧
      ∀ j i, g j * x i * (g j)⁻¹ = (List.ofFn fun k => x k ^ D.expo j k i).prod := by
  set S := NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB
  unfold Ops.normCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hchk, hog⟩, hgs⟩ := h
  have hchk' := hchk
  unfold Ops.check at hchk'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk'
  obtain ⟨⟨⟨-, hprog⟩, houts⟩, hel⟩ := hchk'
  set R := O.regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog with hR
  have hreg : ∀ r < D.base.nregs, Sp.WF R[r]! ∧ Sp.toMat R[r]! ∈ S := fun r hr =>
    Sp.regsOf_ok hprog hr
  set xs := D.base.outs.map fun r => R[r]! with hxs
  have hlen : xs.length = D.base.outs.length := List.length_map _
  have hxsok : ∀ X ∈ xs, Sp.WF X ∧ Sp.toMat X ∈ S := by
    intro X hX
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hX
    exact hreg r (of_decide_eq_true (List.all_eq_true.1 houts r hr))
  have hw : ∀ X ∈ xs, Sp.WF X := fun X hX => (hxsok X hX).1
  have hel' : O.elemOK xs D.base.tests = true := hel
  unfold Ops.elemOK at hel'
  simp only [Bool.and_eq_true] at hel'
  obtain ⟨⟨hcube, hcomm⟩, hkerOK⟩ := hel'
  have hpair := Sp.pairwise_of_commsOK hw hcomm
  have hmem : ∀ i : Fin xs.length, xs[i] ∈ xs := fun i => List.getElem_mem _
  have hcubeM : ∀ i : Fin xs.length, Sp.toMat xs[i] ^ 3 = 1 := by
    intro i
    have hX := hw _ (hmem i)
    have := Sp.toMat_eq (Sp.mul_wf (Sp.mul_wf hX hX) hX) Sp.one_wf
      (List.all_eq_true.1 hcube _ (hmem i))
    rwa [Sp.toMat_mul (Sp.mul_wf hX hX) hX, Sp.toMat_mul hX hX, Sp.toMat_one, ← pow_two,
      ← pow_succ] at this
  let x₀ : Fin xs.length → Sˣ := fun i =>
    unitOf S (hxsok _ (hmem i)).2 (by norm_num : (3 : ℕ) ≠ 0) (hcubeM i)
  have fx : ∀ i, valHom S (x₀ i) = Sp.toMat xs[i] := fun i =>
    valHom_unitOf S (hxsok _ (hmem i)).2 _ (hcubeM i)
  have hgreg : ∀ j : Fin D.gens.length, D.gens[j] < D.base.nregs := by
    intro j
    have := (hgs j j.2).1.1
    rwa [getElem!_pos D.gens j.1 j.2] at this
  let G : Fin D.gens.length → M := fun j => R[D.gens[j]]!
  have hGok : ∀ j, Sp.WF (G j) ∧ Sp.toMat (G j) ∈ S := fun j => hreg _ (hgreg j)
  have hGpow : ∀ j, Sp.toMat (G j) ^ D.og = 1 := by
    intro j
    have := (hgs j j.2).1.2
    rw [getElem!_pos D.gens j.1 j.2] at this
    exact Sp.pow_eq_one_of_check (hGok j).1 this
  let g : Fin D.gens.length → Sˣ := fun j => unitOf S (hGok j).2 hog.ne' (hGpow j)
  have fg : ∀ j, valHom S (g j) = Sp.toMat (G j) := fun j =>
    valHom_unitOf S (hGok j).2 _ (hGpow j)
  have hprod : ∀ e : Fin xs.length → ℕ,
      valHom S (List.ofFn fun k => x₀ k ^ e k).prod =
        (List.ofFn fun k => Sp.toMat xs[k] ^ e k).prod := by
    intro e
    rw [map_list_prod, List.map_ofFn]
    congr 1
  let x : Fin D.base.outs.length → Sˣ := fun i => x₀ (Fin.cast hlen.symm i)
  have hofFn : ∀ e : Fin D.base.outs.length → ℕ,
      (List.ofFn fun k => x k ^ e k).prod =
        (List.ofFn fun k : Fin xs.length => x₀ k ^ e (Fin.cast hlen k)).prod := by
    intro e
    rw [List.ofFn_congr hlen.symm]
  refine ⟨x, g, fun i => unitOf_pow S _ _ _, fun i j => ?_, fun a ha => ?_, fun j i => ?_⟩
  · apply valHom_injective S
    rw [map_mul, map_mul, fx, fx]
    rcases lt_trichotomy (Fin.cast hlen.symm i) (Fin.cast hlen.symm j) with hij | hij | hij
    · exact List.pairwise_iff_getElem.1 hpair _ _ _ _ hij
    · rw [hij]
    · exact (List.pairwise_iff_getElem.1 hpair _ _ _ _ hij).symm
  · intro h1
    have h2 := congrArg (valHom S) h1
    rw [hofFn (fun k => (a k : ℕ)), hprod, map_one] at h2
    refine Sp.ne_one_of_kerOK hw hkerOK (fun k => a (Fin.cast hlen k)) (fun h0 => ha ?_) h2
    funext k
    have := congrFun h0 (Fin.cast hlen.symm k)
    simpa using this
  · rw [mul_inv_eq_iff_eq_mul]
    apply valHom_injective S
    have hi : (i : ℕ) < xs.length := by rw [hlen]; exact i.2
    have hc := (hgs j j.2).2 i hi
    rw [getElem!_pos D.gens j.1 j.2, getElem!_pos xs _ hi] at hc
    have hX := hw _ (hmem (Fin.cast hlen.symm i))
    obtain ⟨wW, eW⟩ := Sp.powProdIdx_spec xs hw fun k => D.expo j k i
    have key := Sp.toMat_of_conjOK (hGok j).1 hX wW hc
    rw [map_mul, map_mul, fg, fx, hofFn (fun k => D.expo j k i), hprod]
    rw [eW] at key
    exact key

end CFSG.SectionRank.OpsSpec

namespace CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest

open Subgroup CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint

theorem card_closure_range_eq_three_pow {G : Type*} [Group G] {r : ℕ} (u : Fin r → G)
    (hpow : ∀ i, u i ^ 3 = 1) (hcomm : ∀ i j, u i * u j = u j * u i)
    (hker : ∀ a : Fin r → Fin 3, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1) :
    Nat.card (closure (Set.range u)) = 3 ^ r := by
  set C := closure (Set.range u)
  have hC : IsMulCommutative C := isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)
  let _ : CommGroup C := { C.toGroup with mul_comm := hC.is_comm.comm }
  let v : Fin r → C := fun i => ⟨u i, subset_closure ⟨i, rfl⟩⟩
  have hv : ∀ i, v i ^ 3 = 1 := fun i => Subtype.ext (by simp [v, hpow])
  let φ := powHom v hv
  have hφ : ∀ t : Fin r → ZMod 3, ((φ (Multiplicative.ofAdd t) : C) : G) =
      (List.ofFn fun i => u i ^ (t i).val).prod := by
    intro t
    rw [powHom_apply, ← List.prod_ofFn]
    have h := map_list_prod C.subtype (List.ofFn fun i => v i ^ (t i).val)
    rw [List.map_ofFn] at h
    exact h
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    rw [mem_bot]
    by_contra hne
    have h1 := hφ (Multiplicative.toAdd t)
    rw [ofAdd_toAdd, ht] at h1
    refine hker (fun i => Multiplicative.toAdd t i) (fun h0 => hne ?_) h1.symm
    exact Multiplicative.toAdd.injective h0
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    have htop : closure (Set.range v) = ⊤ := by
      have h := closure_closure_coe_preimage (k := Set.range u)
      convert h using 2
      ext a
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext hi⟩
    rw [eq_top_iff, ← htop, closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, powHom_single v hv i⟩
  rw [← Nat.card_eq_of_bijective φ ⟨hinj, hsurj⟩]
  simp [Nat.card_eq_fintype_card]

theorem on_normalizer_check :
    (ops3 154).normCheck onNormData = true :=
  Certificates.certificate8007

theorem ON_normalizer_witness :
    ∃ (x : Fin 4 → NativeSporadic.ON) (g : Fin 2 → NativeSporadic.ON),
      (∀ i, x i ^ 3 = 1) ∧ (∀ i j, x i * x j = x j * x i) ∧
      (∀ a : Fin 4 → Fin 3, a ≠ 0 → (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ 1) ∧
      ∀ j i, g j * x i * (g j)⁻¹ = (List.ofFn fun k => x k ^ onNormExpo j k i).prod :=
  (spec3 154).norm_of_check onNormData on_normalizer_check

@[expose] def onPairM (j : Fin 2) (k i : Fin 4) : ℕ := onNormExpo j k i

@[expose] def onPairC (k l : Fin 4) : ℕ :=
  [[0, 0, 0, 1], [0, 0, 2, 2], [0, 1, 0, 0], [2, 1, 0, 0]].getD k [] |>.getD l 0

@[expose] def onPairCs (k l : Fin 4) : List (ℕ × ℕ) :=
  ([[[(2, 1), (1, 2), (2, 4), (1, 5), (1, 7), (2, 8), (1, 14), (2, 16), (1, 18), (1, 19),
        (2, 20)], [(1, 1), (1, 2)], [(2, 1), (1, 2)], []],
    [[(1, 4), (1, 8)], [(1, 1), (1, 4), (2, 6), (2, 7), (1, 8), (1, 13), (1, 14), (2, 17),
        (1, 18), (2, 19), (1, 20)],
      [(2, 1), (2, 2), (1, 4), (1, 6), (2, 7), (1, 8), (1, 13), (2, 17), (1, 19), (1, 20)],
      [(2, 1), (2, 2), (1, 4), (1, 5), (1, 8), (1, 11), (1, 13), (2, 17), (1, 19), (1, 20)]],
    [[(2, 4), (1, 8)], [(1, 1), (1, 2), (2, 4), (1, 6), (1, 7), (2, 8), (2, 13), (1, 17),
        (2, 19), (2, 20)],
      [(1, 1), (1, 4), (1, 5), (2, 6), (2, 7), (1, 8), (1, 13), (1, 14), (2, 17), (1, 18),
        (2, 19), (1, 20)],
      [(1, 1), (1, 4), (2, 5), (1, 7), (1, 8), (1, 11), (1, 13), (1, 14), (2, 17), (1, 18),
        (2, 19), (1, 20)]],
    [[(2, 19)], [(1, 1), (1, 2), (2, 4), (1, 5), (1, 7), (2, 8), (1, 14), (1, 17), (2, 19),
        (2, 20)],
      [(1, 1), (1, 4), (2, 5), (2, 7), (1, 8), (2, 14), (2, 17), (1, 18), (2, 19), (1, 20)],
      [(2, 1), (1, 2), (2, 4), (1, 5), (1, 7), (2, 8), (1, 14), (1, 18), (1, 19), (2, 20)]]] :
      List (List (List (ℕ × ℕ)))).getD k [] |>.getD l []

theorem onPair_lin : ∀ k l : Fin 4,
    Pi.single (k, l) 1 - ((onPairC k l : ℕ) : ZMod 3) • Pi.single ((0 : Fin 4), (3 : Fin 4)) 1 =
      ((onPairCs k l).map fun p => p.1 • (pairingRelations onPairM).getD p.2 0).sum := by
  decide

theorem card_ON_eq_mul : (460815505920 : ℕ) = 3 ^ 4 * 5689080320 := by norm_num

theorem card_center_dvd_three_of_ON_witness {X : Type} [Group X] [Finite X]
    (hX : IsQuasisimple X) (hZ : IsPGroup 3 (center X))
    (hcard : Nat.card (X ⧸ center X) = 460815505920) (x : Fin 4 → X ⧸ center X)
    (g : Fin 2 → X ⧸ center X) (hx3 : ∀ i, x i ^ 3 = 1) (hxc : ∀ i j, x i * x j = x j * x i)
    (hker : ∀ a : Fin 4 → Fin 3, a ≠ 0 → (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ 1)
    (hrel : ∀ j i, g j * x i * (g j)⁻¹ = (List.ofFn fun k => x k ^ onPairM j k i).prod) :
    Nat.card (center X) ∣ 3 := by
  have : Group.IsPerfect X := hX.1
  have hπk := QuotientGroup.ker_mk' (center X)
  have hE : Nat.card (closure (Set.range x)) = 3 ^ 4 :=
    card_closure_range_eq_three_pow x hx3 hxc hker
  have hidx : (closure (Set.range x)).index = 5689080320 := by
    have h1 := (closure (Set.range x)).index_mul_card
    rw [hE, hcard, card_ON_eq_mul] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have hle := card_ker_le_three_of_pairing (QuotientGroup.mk'_surjective (center X)) hπk.le
    (by rw [hπk]; exact hZ) x hx3 hxc (IsPGroup.of_card hE) (by rw [hidx]; norm_num) g onPairM
    hrel 0 3
    onPairC onPairCs onPair_lin
  rw [hπk] at hle
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rw [hk] at hle ⊢
  rcases k with _ | _ | k
  · exact one_dvd 3
  · exact dvd_rfl
  · have : 3 ^ 2 ≤ 3 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem card_center_dvd_three_of_ON
    {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X) (hZ : IsPGroup 3 (center X))
    (e : X ⧸ center X ≃* NativeSporadic.ON) : Nat.card (center X) ∣ 3 := by
  obtain ⟨x, g, hx3, hxc, hker, hrel⟩ := ON_normalizer_witness
  have hprod : ∀ e' : Fin 4 → ℕ, e.symm (List.ofFn fun k => x k ^ e' k).prod =
      (List.ofFn fun k => e.symm (x k) ^ e' k).prod := by
    intro e'
    simp only [map_list_prod, List.map_ofFn, Function.comp_def, map_pow]
  refine card_center_dvd_three_of_ON_witness hX hZ
    ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.ON.card_ON_eq) (fun i => e.symm (x i))
    (fun j => e.symm (g j)) (fun i => by rw [← map_pow, hx3, map_one])
    (fun i j => by rw [← map_mul, ← map_mul, hxc]) (fun a ha h => hker a ha ?_)
    (fun j i => by rw [← map_inv, ← map_mul, ← map_mul, hrel, hprod]; rfl)
  rw [← hprod] at h
  exact (map_eq_one_iff e.symm e.symm.injective).mp h

end CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
