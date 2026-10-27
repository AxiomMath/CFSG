module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Quasithin.Background.F3PathCons
public import CFSG.Quasithin.Recognition.Stroth.MoufangLittleNormal
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNRad

public section

namespace CFSG.Quasithin.Stroth

open CFSG.GH74.BNPair CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Geometry.GeneralizedPolygons

private lemma exists_adj_ne {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hthick : IsThick Γ) {v w : V} (h : Γ.Adj v w) : ∃ u : V, Γ.Adj v u ∧ u ≠ w := by
  classical
  have h3 : 3 ≤ (Γ.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hthick v
  have hw : w ∈ Γ.neighborFinset v := by simpa using h
  have h2 : 2 ≤ ((Γ.neighborFinset v).erase w).card := by
    rw [Finset.card_erase_of_mem hw]; omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < ((Γ.neighborFinset v).erase w).card)
  exact ⟨u, by simpa using (Finset.mem_of_mem_erase hu), Finset.ne_of_mem_erase hu⟩

private lemma exists_noBack_path_to {V : Type} {Γ : SimpleGraph V}
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u : V, Γ.Adj v u ∧ u ≠ w)
    {y u : V} (hyu : Γ.Adj y u) :
    ∀ n : ℕ, 1 ≤ n → ∃ p : GPath Γ n, p.NoBack ∧ p (n - 1) = y ∧ p n = u := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    have hnb : (GPath.ofAdj hyu).NoBack := by
      intro i hi
      omega
    exact ⟨GPath.ofAdj hyu, hnb, by simp, by simp⟩
  | succ n hn ih =>
    obtain ⟨p, hp, hpy, hpu⟩ := ih
    have hadj : Γ.Adj (p 0) (p 1) := p.adj 0 (by omega)
    obtain ⟨z, hz, hz1⟩ := hne (p 0) (p 1) hadj
    refine ⟨GPath.cons z p hz.symm, GPath.noBack_cons z p hz.symm hp hz1, ?_, ?_⟩
    · rw [show n + 1 - 1 = (n - 1) + 1 by omega, GPath.cons_succ, hpy]
    · rw [GPath.cons_succ, hpu]

private lemma pathRootGroup_smul_end {V : Type} {Γ : SimpleGraph V} {D : Type} [Group D]
    [MulAction D V] {n : ℕ} (hn : 2 ≤ n) {p : GPath Γ n} {g : D}
    (hg : g ∈ pathRootGroup D Γ p) : g • p n = p n := by
  have hfix : g ∈ fixingSubgroup D (Γ.neighborSet (p (n - 1))) := by
    simp only [pathRootGroup, Subgroup.mem_iInf] at hg
    exact hg (n - 1) ⟨by omega, le_rfl⟩
  refine (mem_fixingSubgroup_iff (M := D)).1 hfix (p n) ?_
  rw [SimpleGraph.mem_neighborSet]
  have h := p.adj (n - 1) (by omega)
  rwa [show n - 1 + 1 = n by omega] at h

private lemma littleGroup_stabilizer_transitive {V : Type} [Fintype V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj] {D : Type} [Group D] [MulAction D V] [GraphAction D Γ] {n : ℕ}
    (hn : 3 ≤ n) (hpoly : IsGeneralizedPolygon Γ n) (hthick : IsThick Γ)
    (hmouf : MoufangCondition D Γ n) {u w w' : V}
    (hw : Γ.Adj u w) (hw' : Γ.Adj u w') :
    ∃ l ∈ littleGroup D Γ n, l • u = u ∧ l • w = w' := by
  classical
  rcases eq_or_ne w w' with rfl | hne
  · exact ⟨1, one_mem _, by simp, by simp⟩
  obtain ⟨y, hy, hyw, hyw'⟩ : ∃ y : V, Γ.Adj u y ∧ y ≠ w ∧ y ≠ w' := by
    have hcard : 3 ≤ (Γ.neighborFinset u).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hthick u
    have hw1 : w ∈ Γ.neighborFinset u := by simpa using hw
    have hw2 : w' ∈ Γ.neighborFinset u := by simpa using hw'
    have h2 : 2 ≤ ((Γ.neighborFinset u).erase w).card := by
      rw [Finset.card_erase_of_mem hw1]; omega
    have hw'1 : w' ∈ (Γ.neighborFinset u).erase w :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, hw2⟩
    have h3 : 1 ≤ (((Γ.neighborFinset u).erase w).erase w').card := by
      rw [Finset.card_erase_of_mem hw'1]; omega
    obtain ⟨z, hz⟩ :=
      Finset.card_pos.mp (by omega : 0 < (((Γ.neighborFinset u).erase w).erase w').card)
    exact ⟨z, by simpa using (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)),
      Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz), Finset.ne_of_mem_erase hz⟩
  obtain ⟨p, hpnb, hp1, hp2⟩ :=
    exists_noBack_path_to (fun v w h => exists_adj_ne hthick h) hy.symm n (by omega)
  have hpu : Γ.Adj (p n) w := hp2.symm ▸ hw
  have hpu' : Γ.Adj (p n) w' := hp2.symm ▸ hw'
  have hne1 : w ≠ p (n - 1) := fun h => hyw ((h.trans hp1).symm)
  have hne2 : w' ≠ p (n - 1) := fun h => hyw' ((h.trans hp1).symm)
  obtain ⟨g, hgfix, hgw⟩ := hmouf p hpnb w w' hpu hpu' hne1 hne2
  have hgmem : g ∈ pathRootGroup D Γ p := by
    simp only [pathRootGroup, Subgroup.mem_iInf]
    intro i hi
    refine (mem_fixingSubgroup_iff (M := D)).2 ?_
    intro x hx
    exact hgfix i hi.1 hi.2 x (by simpa using hx)
  refine ⟨g, pathRootGroup_le_littleGroup hpnb hgmem, ?_, hgw⟩
  have h := pathRootGroup_smul_end (n := n) (by omega) hgmem
  rwa [hp2] at h



private lemma map_aut_eq_of_normal_sylow {G : Type} [Group G] [Finite G]
    {M P : Subgroup G} (hPM : P ≤ M) (hP2 : IsPGroup 2 P) (hPodd : ¬ 2 ∣ P.relIndex M)
    (hPn : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P) (φ : G ≃* G)
    (hφM : M.map φ.toMonoidHom = M) : P.map φ.toMonoidHom = P := by
  have hSylM : IsSylowTwoOf P M := ⟨hPM, hP2, hPodd⟩
  have hSylM' : IsSylowTwoOf (P.map φ.toMonoidHom) M := by
    have h := hSylM.map_equiv φ
    rwa [hφM] at h
  obtain ⟨m, hmM, hmeq⟩ := B6.isSylowTwoOf_exists_conj hSylM hSylM'
  rw [hmeq]
  refine B6.conjSub_eq_self (Subgroup.mem_normalizer_iff.mpr ?_)
  intro x
  constructor
  · exact fun hx => hPn m hmM x hx
  · intro hx
    have h := hPn m⁻¹ (M.inv_mem hmM) (m * x * m⁻¹) hx
    rwa [show m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x by group] at h

private lemma map_map_conj {G H : Type} [Group G] [Group H] (f : G →* H)
    (S : Subgroup G) (g : G) :
    (S.map (MulAut.conj g)).map f =
      (S.map f).map (MulAut.conj (f g)) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

private lemma isSylowTwoOf_map_subtype {A : Type} [Group A] {L : Subgroup A}
    {S U : Subgroup ↥L} (hSU : S ≤ U) (hS : IsSylowTwoOf S U) :
    IsSylowTwoOf (S.map L.subtype) (U.map L.subtype) := by
  refine ⟨Subgroup.map_mono hSU, hS.2.1.map L.subtype, ?_⟩
  show ¬ 2 ∣ (S.map L.subtype).relIndex (U.map L.subtype)
  rw [Subgroup.relIndex_map_map_of_injective (f := L.subtype) S U L.subtype_injective]
  show ¬ 2 ∣ S.relIndex U
  exact hS.2.2

private lemma simsG4_twoPrimeResidualOf_le_b6 {G : Type} [Group G] [Finite G]
    (H : Subgroup G) :
    CFSG.Quasithin.SimsG4.twoPrimeResidualOf H ≤ CFSG.Quasithin.twoPrimeResidual H := by
  intro x hx
  rw [CFSG.Quasithin.SimsG4.twoPrimeResidualOf, Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [CFSG.Quasithin.twoPrimeResidual]
  refine Subgroup.mem_iInf.mpr fun N => Subgroup.mem_iInf.mpr fun hN => ?_
  obtain ⟨hNH, hHnorm, hNodd⟩ := hN
  have hN' : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHnorm
  have hNodd' : Odd (N.subgroupOf H).index := by
    have h : ¬ 2 ∣ (N.subgroupOf H).index := hNodd
    exact Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using h)
  exact Subgroup.mem_sInf.mp hy (N.subgroupOf H) ⟨hN', hNodd'⟩

private lemma exists_mul_eq_of_normal {G : Type} [Group G] [Finite G]
    {K N P : Subgroup G} (hNK : N ≤ K) (hKn : K ≤ Subgroup.normalizer (N : Set G))
    (hP : IsSylowTwoOf P K) (hPN : P ≤ N) {k : G} (hk : k ∈ K) :
    ∃ a ∈ N, ∃ b ∈ Subgroup.normalizer (P : Set G), a * b = k := by
  have hP2N : IsSylowTwoOf P N := B6.isSylowTwoOf_mono hP hPN hNK
  have hkP : IsSylowTwoOf (P.map (MulAut.conj k).toMonoidHom) N := by
    have h1 := hP.map_equiv (MulAut.conj k)
    have hKk : K.map (MulAut.conj k).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hk)
    rw [hKk] at h1
    refine B6.isSylowTwoOf_mono h1 (fun x hx => ?_) hNK
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    have := (Subgroup.mem_normalizer_iff.mp (hKn hk) p).mp (hPN hp)
    simpa [MulAut.conj_apply] using this
  obtain ⟨n, hnN, hnP⟩ := B6.isSylowTwoOf_exists_conj hkP hP2N
  have heqP : B6.conjSub n (P.map (MulAut.conj k).toMonoidHom) = P := hnP.symm
  have hnk : n * k ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 : k * y * k⁻¹ ∈ P.map (MulAut.conj k).toMonoidHom :=
        ⟨y, hy, MulAut.conj_apply k y⟩
      have h2 : n * (k * y * k⁻¹) * n⁻¹ ∈
          B6.conjSub n (P.map (MulAut.conj k).toMonoidHom) := by
        rw [B6.mem_conjSub]
        rwa [show n⁻¹ * (n * (k * y * k⁻¹) * n⁻¹) * n = k * y * k⁻¹ by group]
      rw [heqP] at h2
      simpa only [mul_assoc, mul_inv_rev, inv_inv] using h2
    · intro hy
      have h2 : n * (k * y * k⁻¹) * n⁻¹ ∈
          B6.conjSub n (P.map (MulAut.conj k).toMonoidHom) := by
        rw [heqP]
        simpa only [mul_assoc, mul_inv_rev, inv_inv] using hy
      have h1 : k * y * k⁻¹ ∈ P.map (MulAut.conj k).toMonoidHom := by
        have := B6.mem_conjSub.mp h2
        rwa [show n⁻¹ * (n * (k * y * k⁻¹) * n⁻¹) * n = k * y * k⁻¹ by group] at this
      obtain ⟨p, hp, hpeq⟩ := Subgroup.mem_map.mp h1
      have h3 : y = p := by
        have h2 : k * y * k⁻¹ = k * p * k⁻¹ := by
          rw [← hpeq]
          simpa using (MulAut.conj_apply k p)
        have := congrArg (fun z => k⁻¹ * z * k) h2
        simpa [mul_assoc] using this
      rwa [h3]
  refine ⟨n⁻¹, N.inv_mem hnN, n * k, hnk, ?_⟩
  group

private lemma twoPrimeResidual_le {D : Type} [Group D] [Finite D]
    {K W : Subgroup D} (h : ∀ S : Subgroup D, IsSylowTwoOf S K → S ≤ W) :
    CFSG.Quasithin.twoPrimeResidual K ≤ W := by
  obtain ⟨T, hT, -⟩ := B6.exists_isSylowTwoOf_ge (J := K) (X := ⊥)
    (IsPGroup.of_card (n := 0) (by simp)) bot_le
  rw [← CFSG.Quasithin.conjClosure_eq_twoPrimeResidual hT, CFSG.Quasithin.conjClosure,
    Subgroup.closure_le]
  rintro z ⟨x, hx, t, ht, rfl⟩
  have hxT : IsSylowTwoOf (T.map (MulAut.conj x).toMonoidHom) K := by
    have h1 := hT.map_equiv (MulAut.conj x)
    have hKx : K.map (MulAut.conj x).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx)
    rwa [hKx] at h1
  have := h _ hxT (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
  simpa [MulAut.conj_apply] using this

private lemma le_of_residual_le {D : Type} [Group D] [Finite D]
    {K N U W : Subgroup D} (hUN : U ≤ N) (hNK : N ≤ K)
    (hKnorm : K ≤ Subgroup.normalizer (N : Set D)) (hUK : IsSylowTwoOf U K)
    (hNW : N ≤ W) (hnormW : K ⊓ Subgroup.normalizer (U : Set D) ≤ W) : K ≤ W := by
  intro k hk
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_eq_of_normal hNK hKnorm hUK hUN hk
  have hbK : b ∈ K := by
    have h : b = a⁻¹ * k := by rw [← hab]; group
    rw [h]
    exact K.mul_mem (K.inv_mem (hNK ha)) hk
  rw [← hab]
  exact W.mul_mem (hNW ha) (hnormW ⟨hbK, hb⟩)

private lemma conj_sylow_le_of_transitive
    {V : Type} {Γ : SimpleGraph V} {D : Type} [Group D] [Finite D] [MulAction D V]
    [GraphAction D Γ] {u v : V} {L Du Dv M U W : Subgroup D}
    {T : Type} [Group T] {ψ : T →* D}
    (huv : Γ.Adj u v) (hLnormal : L.Normal)
    (hmemDu : ∀ d : D, d ∈ Du ↔ d • u = u)
    (hmemDv : ∀ d : D, d ∈ Dv ↔ d • v = v)
    (hDu_conj : ∀ y ∈ Du, ∀ w ∈ Du, y * w * y⁻¹ ∈ Du)
    (hDv_conj : ∀ y ∈ Dv, ∀ w ∈ Dv, y * w * y⁻¹ ∈ Dv)
    (hmemM : ∀ w : D, w ∈ M ↔ w ∈ L ∧ w ∈ Du ∧ w ∈ Dv)
    (hUPM : U ≤ M) (hU2 : IsPGroup 2 U) (hUodd : ¬ 2 ∣ U.relIndex M)
    (hUnorm : ∀ m ∈ M, ∀ p ∈ U, m * p * m⁻¹ ∈ U)
    (hψW : ψ.range = W) (hWDu : W ≤ Du) (hUleW : U ≤ W)
    (htrans : ∀ w : V, Γ.Adj u w → ∃ g : T, ψ g • v = w)
    {x : D} (hxL : x ∈ L) (hxDu : x ∈ Du) :
    U.map (MulAut.conj x).toMonoidHom ≤ W := by
  have hxuv : x • u = u := (hmemDu x).mp hxDu
  have hadj : Γ.Adj u (x • v) := by
    have h := (GraphAction.adj_smul x u v).mpr huv
    rwa [hxuv] at h
  obtain ⟨g, hg⟩ := htrans (x • v) hadj
  have hψgW : ψ g ∈ W := hψW ▸ MonoidHom.mem_range.mpr ⟨g, rfl⟩
  have hψgDu : ψ g ∈ Du := hWDu hψgW
  have hyDu : (ψ g)⁻¹ * x ∈ Du := Du.mul_mem (Du.inv_mem hψgDu) hxDu
  have hyDv : (ψ g)⁻¹ * x ∈ Dv := by
    rw [hmemDv, mul_smul, ← hg, inv_smul_smul]
  have hφM : M.map (MulAut.conj ((ψ g)⁻¹ * x)).toMonoidHom = M := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.mem_normalizer_iff.mpr ?_)
    intro w
    constructor
    · intro hw
      obtain ⟨hwL, hwDu, hwDv⟩ := (hmemM w).mp hw
      exact (hmemM _).mpr
        ⟨hLnormal.conj_mem w hwL ((ψ g)⁻¹ * x), hDu_conj _ hyDu w hwDu,
          hDv_conj _ hyDv w hwDv⟩
    · intro hw
      obtain ⟨hwL, hwDu, hwDv⟩ := (hmemM _).mp hw
      have hyiDu : ((ψ g)⁻¹ * x)⁻¹ ∈ Du := Du.inv_mem hyDu
      have hyiDv : ((ψ g)⁻¹ * x)⁻¹ ∈ Dv := Dv.inv_mem hyDv
      have hw' : ((ψ g)⁻¹ * x)⁻¹ * ((ψ g)⁻¹ * x * w * ((ψ g)⁻¹ * x)⁻¹) *
          ((ψ g)⁻¹ * x) ∈ M := by
        have h := (hmemM _).mpr ⟨hLnormal.conj_mem _ hwL _, hDu_conj _ hyiDu _ hwDu,
          hDv_conj _ hyiDv _ hwDv⟩
        simpa only [inv_inv] using h
      rwa [show ((ψ g)⁻¹ * x)⁻¹ * ((ψ g)⁻¹ * x * w * ((ψ g)⁻¹ * x)⁻¹) *
        ((ψ g)⁻¹ * x) = w by group] at hw'
  have hyconj : U.map (MulAut.conj ((ψ g)⁻¹ * x)).toMonoidHom = U :=
    map_aut_eq_of_normal_sylow hUPM hU2 hUodd hUnorm _ hφM
  intro z hz
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hz
  have hyp : (ψ g)⁻¹ * x * p * ((ψ g)⁻¹ * x)⁻¹ ∈ U := by
    have h : (ψ g)⁻¹ * x * p * ((ψ g)⁻¹ * x)⁻¹ ∈
        U.map (MulAut.conj ((ψ g)⁻¹ * x)).toMonoidHom :=
      ⟨p, hp, MulAut.conj_apply _ _⟩
    rwa [hyconj] at h
  suffices h : (MulAut.conj x).toMonoidHom p =
      ψ g * ((ψ g)⁻¹ * x * p * ((ψ g)⁻¹ * x)⁻¹) * (ψ g)⁻¹ by
    rw [h]
    exact W.mul_mem (W.mul_mem hψgW (hUleW hyp)) (W.inv_mem hψgW)
  rw [show (MulAut.conj x).toMonoidHom p = x * p * x⁻¹ from MulAut.conj_apply x p]
  have hx : x = ψ g * ((ψ g)⁻¹ * x) := by group
  rw [hx]; group

private lemma normalizer_map_subtype {A : Type} [Group A] {L : Subgroup A}
    (S : Subgroup ↥L) :
    Subgroup.normalizer (S.map L.subtype : Set A) ⊓ L =
      (Subgroup.normalizer (S : Set ↥L)).map L.subtype := by
  have hkey : ∀ x : ↥L, (x ∈ Subgroup.normalizer (S : Set ↥L)) ↔
      (S.map L.subtype).map (MulAut.conj (L.subtype x)) = S.map L.subtype := by
    intro x
    constructor
    · intro h
      have h1 : S.map (MulAut.conj x) = S :=
        (Subgroup.mem_normalizer_iff_map_conj_eq (H := S)).mp h
      have h2 := map_map_conj L.subtype S x
      rw [h1] at h2
      exact h2.symm
    · intro h
      have h2 := map_map_conj L.subtype S x
      rw [h] at h2
      exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := S)).mpr
        (Subgroup.map_injective L.subtype_injective h2)
  ext x
  constructor
  · rintro ⟨hxN, hxL⟩
    rw [Subgroup.mem_map]
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    exact (hkey ⟨x, hxL⟩).mpr
      ((Subgroup.mem_normalizer_iff_map_conj_eq (H := S.map L.subtype)).mp hxN)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff_map_conj_eq (H := S.map L.subtype)).mpr ?_, y.2⟩
    exact (hkey y).mp hy

theorem stabilizersOfPolygon (n : ℕ) : StabilizersOfPolygon n := by
  intro X instX P1 P2 V instV Γ instAdj D instD instFD instMul instGA
    hn hpoly hthick hmouf hLnorm u v ψ₁ ψ₂ hagree hψ₁u hψ₂v hgen hint1 hint2
    htrans1 htrans2 R hRB hori hU hSyl hM3
  classical
  have hLnormal : (littleGroup D Γ n).Normal := hLnorm
  haveI : (littleGroup D Γ n).Normal := hLnormal
  have hmemDu : ∀ d : D, d ∈ ((MulAction.stabilizer D u)) ↔ d • u = u := by
    intro d; rw [MulAction.mem_stabilizer_iff]
  have hmemDv : ∀ d : D, d ∈ ((MulAction.stabilizer D v)) ↔ d • v = v := by
    intro d; rw [MulAction.mem_stabilizer_iff]
  have hDu_conj : ∀ y ∈ ((MulAction.stabilizer D u)), ∀ w ∈ ((MulAction.stabilizer D u)),
      y * w * y⁻¹ ∈ ((MulAction.stabilizer D u)) :=
        fun y hy w hw =>
          ((MulAction.stabilizer D u)).mul_mem
            (((MulAction.stabilizer D u)).mul_mem hy hw)
            (((MulAction.stabilizer D u)).inv_mem hy)
  have hDv_conj : ∀ y ∈ ((MulAction.stabilizer D v)), ∀ w ∈ ((MulAction.stabilizer D v)),
      y * w * y⁻¹ ∈ ((MulAction.stabilizer D v)) :=
        fun y hy w hw =>
          ((MulAction.stabilizer D v)).mul_mem
            (((MulAction.stabilizer D v)).mul_mem hy hw)
            (((MulAction.stabilizer D v)).inv_mem hy)
  have hBψ_le_ψ₁ : ((psiB P2 ψ₁).range) ≤ ψ₁.range := by
    intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    exact MonoidHom.mem_range.mpr ⟨Subgroup.inclusion inf_le_left a, rfl⟩
  have hBψ_le_Du : ((psiB P2 ψ₁).range) ≤ ((MulAction.stabilizer D u)) := by
    calc ((psiB P2 ψ₁).range) = ψ₂.range ⊓ ((MulAction.stabilizer D u)) := hint2.symm
      _ ≤ ((MulAction.stabilizer D u)) := inf_le_right
  have hBψ_le_Dv : ((psiB P2 ψ₁).range) ≤ ((MulAction.stabilizer D v)) := by
    calc ((psiB P2 ψ₁).range) = ψ₁.range ⊓ ((MulAction.stabilizer D v)) := hint1.symm
      _ ≤ ((MulAction.stabilizer D v)) := inf_le_right
  have hBψ_le_ψ₂ : ((psiB P2 ψ₁).range) ≤ ψ₂.range := by
    calc ((psiB P2 ψ₁).range) = ψ₂.range ⊓ ((MulAction.stabilizer D u)) := hint2.symm
      _ ≤ ψ₂.range := inf_le_left
  have hU_le_L : (R.U.map (littleGroup D Γ n).subtype) ≤ (littleGroup D Γ n) :=
    Subgroup.map_subtype_le _
  have hU_le_Du : (R.U.map (littleGroup D Γ n).subtype) ≤ ((MulAction.stabilizer D u)) :=
    hU.trans hBψ_le_Du
  have hU_le_Dv : (R.U.map (littleGroup D Γ n).subtype) ≤ ((MulAction.stabilizer D v)) :=
    hU.trans hBψ_le_Dv
  have hU_le_ψ₁ : (R.U.map (littleGroup D Γ n).subtype) ≤ ψ₁.range := hU.trans hBψ_le_ψ₁
  have hSylL : IsSylowTwoOf (R.U.map (littleGroup D Γ n).subtype) (littleGroup D Γ n) := by
    refine ⟨hU_le_L, hSyl.2.1.map (littleGroup D Γ n).subtype, ?_⟩
    have hrel : (R.U.map (littleGroup D Γ n).subtype).relIndex (littleGroup D Γ n) =
        R.U.relIndex ⊤ := by
      have h := Subgroup.relIndex_map_map_of_injective (f := (littleGroup D Γ n).subtype) R.U
        (⊤ : Subgroup ↥(littleGroup D Γ n)) (littleGroup D Γ n).subtype_injective
      rwa [Subgroup.map_top, Subgroup.range_subtype] at h
    show ¬ 2 ∣ (R.U.map (littleGroup D Γ n).subtype).relIndex (littleGroup D Γ n)
    rw [hrel]
    exact hSyl.2.2
  have hUK : IsSylowTwoOf (R.U.map (littleGroup D Γ n).subtype)
      ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D u))) :=
    B6.isSylowTwoOf_mono hSylL (le_inf hU_le_L hU_le_Du) inf_le_left
  have hUKv : IsSylowTwoOf (R.U.map (littleGroup D Γ n).subtype)
      ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D v))) :=
    B6.isSylowTwoOf_mono hSylL (le_inf hU_le_L hU_le_Dv) inf_le_left
  have huv : Γ.Adj u v := by
    obtain ⟨w, hw⟩ : ∃ w, Γ.Adj u w := by
      have h3 : 3 ≤ (Γ.neighborFinset u).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hthick u
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (Γ.neighborFinset u).card)
      exact ⟨w, by simpa using hw⟩
    obtain ⟨g, hg⟩ := htrans1 w hw
    have hgDu : ψ₁ g ∈ ((MulAction.stabilizer D u)) := hψ₁u (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    have hinv : (ψ₁ g)⁻¹ • u = u := (hmemDu _).mp (((MulAction.stabilizer D u)).inv_mem hgDu)
    have h := (GraphAction.adj_smul (ψ₁ g)⁻¹ u w).mpr hw
    rwa [hinv, ← hg, inv_smul_smul] at h
  have huve : Γ.Adj v u := huv.symm
  have hSylRB : IsSylowTwoOf R.U R.B := B6.isSylowTwoOf_mono hSyl (RankTwoSystem.U_le_B R) le_top
  have hUPM : (R.U.map (littleGroup D Γ n).subtype) ≤
      ((R.B.map (littleGroup D Γ n).subtype)) := Subgroup.map_mono hSylRB.1
  have hmemM : ∀ w : D, w ∈ ((R.B.map (littleGroup D Γ n).subtype)) ↔
      w ∈ (littleGroup D Γ n) ∧ w ∈ ((MulAction.stabilizer D u)) ∧
        w ∈ ((MulAction.stabilizer D v)) := by
    intro w
    constructor
    · intro hw
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hw
      have hb' : (b : D) ∈ ((MulAction.stabilizer D u)) ⊓ ((MulAction.stabilizer D v)) := by
        have h := hb
        rw [hRB] at h
        exact Subgroup.mem_subgroupOf.mp h
      exact ⟨b.2, hb'.1, hb'.2⟩
    · rintro ⟨hwL, hwDu, hwDv⟩
      refine Subgroup.mem_map.mpr ⟨⟨w, hwL⟩, ?_, rfl⟩
      rw [hRB]
      exact Subgroup.mem_subgroupOf.mpr ⟨hwDu, hwDv⟩
  have hUoddM : ¬ 2 ∣ (R.U.map (littleGroup D Γ n).subtype).relIndex
      ((R.B.map (littleGroup D Γ n).subtype)) := by
    have h := Subgroup.relIndex_map_map_of_injective (f := (littleGroup D Γ n).subtype) R.U R.B
      (littleGroup D Γ n).subtype_injective
    rw [show R.B.map (littleGroup D Γ n).subtype =
      ((R.B.map (littleGroup D Γ n).subtype)) from rfl] at h
    rw [h]
    exact hSylRB.2.2
  have hUnormM : ∀ m ∈ ((R.B.map (littleGroup D Γ n).subtype)),
      ∀ p ∈ (R.U.map (littleGroup D Γ n).subtype),
        m * p * m⁻¹ ∈ (R.U.map (littleGroup D Γ n).subtype) := by
    intro m hm p hp
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hm
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hp
    have hb' : b ∈ Subgroup.normalizer (R.U : Set ↥(littleGroup D Γ n)) :=
      CFSG.Quasithin.H13.F431.BN.B_le_normalizer_U R hb
    have hbr : b * r * b⁻¹ ∈ R.U := (Subgroup.mem_normalizer_iff.mp hb' r).mp hr
    exact Subgroup.mem_map.mpr ⟨b * r * b⁻¹, hbr, by simp [mul_assoc]⟩
  have hNormU : Subgroup.normalizer ((R.U.map (littleGroup D Γ n).subtype) : Set D) ⊓
      (littleGroup D Γ n) = ((R.B.map (littleGroup D Γ n).subtype)) := by
    rw [normalizer_map_subtype, CFSG.Quasithin.H13.F431.BN.normalizer_U_eq_B R]
  have hconj_le : ∀ x : D, x ∈ (littleGroup D Γ n) → x ∈ ((MulAction.stabilizer D u)) →
      (R.U.map (littleGroup D Γ n).subtype).map (MulAut.conj x).toMonoidHom ≤ ψ₁.range := by
    intro x hxL hxDu
    exact conj_sylow_le_of_transitive (u := u) (v := v)
      (M := ((R.B.map (littleGroup D Γ n).subtype)))
      (U := (R.U.map (littleGroup D Γ n).subtype)) (W := ψ₁.range)
      (T := ↥P1) (ψ := ψ₁) huv hLnormal hmemDu hmemDv hDu_conj hDv_conj hmemM hUPM
      (hSyl.2.1.map (littleGroup D Γ n).subtype) hUoddM hUnormM rfl hψ₁u hU_le_ψ₁
      htrans1 hxL hxDu
  have hconj_le_v : ∀ x : D, x ∈ (littleGroup D Γ n) → x ∈ ((MulAction.stabilizer D v)) →
      (R.U.map (littleGroup D Γ n).subtype).map (MulAut.conj x).toMonoidHom ≤ ψ₂.range := by
    intro x hxL hxDv
    exact conj_sylow_le_of_transitive (u := v) (v := u)
      (M := ((R.B.map (littleGroup D Γ n).subtype)))
      (U := (R.U.map (littleGroup D Γ n).subtype)) (W := ψ₂.range)
      (T := ↥P2) (ψ := ψ₂) huve hLnormal hmemDv hmemDu hDv_conj hDu_conj
      (fun w => (hmemM w).trans (by tauto)) hUPM
      (hSyl.2.1.map (littleGroup D Γ n).subtype) hUoddM hUnormM rfl hψ₂v
      (hU.trans hBψ_le_ψ₂) htrans2 hxL hxDv
  have step2 : ∀ S : Subgroup D,
      IsSylowTwoOf S ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D u))) →
        S ≤ ψ₁.range := by
    intro S hS
    obtain ⟨g, hg, hSg⟩ := B6.isSylowTwoOf_exists_conj hUK hS
    rw [hSg]
    simpa [B6.conjSub] using hconj_le (g : D) hg.1 hg.2
  have step2v : ∀ S : Subgroup D,
      IsSylowTwoOf S ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D v))) →
        S ≤ ψ₂.range := by
    intro S hS
    obtain ⟨g, hg, hSg⟩ := B6.isSylowTwoOf_exists_conj hUKv hS
    rw [hSg]
    simpa [B6.conjSub] using hconj_le_v (g : D) hg.1 hg.2
  have hO2 : ∀ (H : Subgroup ↥(littleGroup D Γ n)) (W : Subgroup D),
      (∀ S : Subgroup D, IsSylowTwoOf S (H.map (littleGroup D Γ n).subtype) → S ≤ W) →
      ((CFSG.Quasithin.SimsG4.twoPrimeResidualOf H).map (littleGroup D Γ n).subtype) ≤ W := by
    intro H W hW
    rw [Subgroup.map_le_iff_le_comap]
    refine (simsG4_twoPrimeResidualOf_le_b6 H).trans ?_
    obtain ⟨T, hT, -⟩ := B6.exists_isSylowTwoOf_ge (J := H) (X := ⊥)
      (IsPGroup.of_card (n := 0) (by simp)) bot_le
    rw [← CFSG.Quasithin.conjClosure_eq_twoPrimeResidual hT, CFSG.Quasithin.conjClosure,
      Subgroup.closure_le]
    rintro z ⟨x, hx, t, ht, rfl⟩
    have hxT : IsSylowTwoOf (B6.conjSub x T) H := by
      have h1 := hT.map_equiv (MulAut.conj x)
      have hHx : H.map (MulAut.conj x).toMonoidHom = H := by
        ext y
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact H.mul_mem (H.mul_mem hx hw) (H.inv_mem hx)
        · intro hy
          refine ⟨x⁻¹ * y * x, H.mul_mem (H.mul_mem (H.inv_mem hx) hy) hx, ?_⟩
          show x * (x⁻¹ * y * x) * x⁻¹ = y
          group
      rwa [hHx] at h1
    have hSyl' : IsSylowTwoOf ((B6.conjSub x T).map (littleGroup D Γ n).subtype)
        (H.map (littleGroup D Γ n).subtype) :=
      isSylowTwoOf_map_subtype hxT.1 hxT
    have hz : (littleGroup D Γ n).subtype (x * t * x⁻¹) ∈
        (B6.conjSub x T).map (littleGroup D Γ n).subtype := by
      refine Subgroup.mem_map.mpr ⟨x * t * x⁻¹, ?_, rfl⟩
      rw [B6.mem_conjSub]
      rwa [show x⁻¹ * (x * t * x⁻¹) * x = t by group]
    exact hW _ hSyl' hz
  have hM3' : ((R.B.map (littleGroup D Γ n).subtype)) ≤
      ((CFSG.Quasithin.SimsG4.twoPrimeResidualOf R.P₁).map (littleGroup D Γ n).subtype ⊓
      R.P₂.map (littleGroup D Γ n).subtype) ⊔
      ((CFSG.Quasithin.SimsG4.twoPrimeResidualOf R.P₂).map (littleGroup D Γ n).subtype ⊓
        R.P₁.map (littleGroup D Γ n).subtype) := by
    have h := Subgroup.map_mono (f := (littleGroup D Γ n).subtype) hM3
    simpa only [Subgroup.map_sup,
      Subgroup.map_inf _ _ _ (littleGroup D Γ n).subtype_injective] using h
  have hM_le_Bψ : ((R.B.map (littleGroup D Γ n).subtype)) ≤ ((psiB P2 ψ₁).range) := by
    rcases hori with ⟨hP1, hP2⟩ | ⟨hP1, hP2⟩
    · have hK1 : R.P₁.map (littleGroup D Γ n).subtype =
          (littleGroup D Γ n) ⊓ ((MulAction.stabilizer D u)) := by
        rw [hP1, Subgroup.subgroupOf_map_subtype, inf_comm]
      have hK2 : R.P₂.map (littleGroup D Γ n).subtype =
          (littleGroup D Γ n) ⊓ ((MulAction.stabilizer D v)) := by
        rw [hP2, Subgroup.subgroupOf_map_subtype, inf_comm]
      have hP1ψ : (CFSG.Quasithin.SimsG4.twoPrimeResidualOf R.P₁).map (littleGroup D Γ n).subtype ≤
          ψ₁.range := by
        refine hO2 R.P₁ ψ₁.range ?_
        intro S hS
        rw [hK1] at hS
        exact step2 S hS
      have hP2ψ : (CFSG.Quasithin.SimsG4.twoPrimeResidualOf R.P₂).map (littleGroup D Γ n).subtype ≤
          ψ₂.range := by
        refine hO2 R.P₂ ψ₂.range ?_
        intro S hS
        rw [hK2] at hS
        exact step2v S hS
      refine hM3'.trans (sup_le ?_ ?_)
      · have hle : R.P₂.map (littleGroup D Γ n).subtype ≤ ((MulAction.stabilizer D v)) := by
          rw [hK2]; exact inf_le_right
        exact (inf_le_inf hP1ψ hle).trans (le_of_eq hint1)
      · have hle : R.P₁.map (littleGroup D Γ n).subtype ≤ ((MulAction.stabilizer D u)) := by
          rw [hK1]; exact inf_le_right
        exact (inf_le_inf hP2ψ hle).trans (le_of_eq hint2)
    · have hK1 : R.P₁.map (littleGroup D Γ n).subtype =
          (littleGroup D Γ n) ⊓ ((MulAction.stabilizer D v)) := by
        rw [hP1, Subgroup.subgroupOf_map_subtype, inf_comm]
      have hK2 : R.P₂.map (littleGroup D Γ n).subtype =
          (littleGroup D Γ n) ⊓ ((MulAction.stabilizer D u)) := by
        rw [hP2, Subgroup.subgroupOf_map_subtype, inf_comm]
      have hP1ψ : (CFSG.Quasithin.SimsG4.twoPrimeResidualOf R.P₁).map (littleGroup D Γ n).subtype ≤
          ψ₂.range := by
        refine hO2 R.P₁ ψ₂.range ?_
        intro S hS
        rw [hK1] at hS
        exact step2v S hS
      have hP2ψ : (CFSG.Quasithin.SimsG4.twoPrimeResidualOf R.P₂).map (littleGroup D Γ n).subtype ≤
          ψ₁.range := by
        refine hO2 R.P₂ ψ₁.range ?_
        intro S hS
        rw [hK2] at hS
        exact step2 S hS
      refine hM3'.trans (sup_le ?_ ?_)
      · have hle : R.P₂.map (littleGroup D Γ n).subtype ≤ ((MulAction.stabilizer D u)) := by
          rw [hK2]; exact inf_le_right
        exact (inf_le_inf hP1ψ hle).trans (le_of_eq hint2)
      · have hle : R.P₁.map (littleGroup D Γ n).subtype ≤ ((MulAction.stabilizer D v)) := by
          rw [hK1]; exact inf_le_right
        exact (inf_le_inf hP2ψ hle).trans (le_of_eq hint1)
  have hK_le_norm : (littleGroup D Γ n) ⊓ ((MulAction.stabilizer D u)) ≤ Subgroup.normalizer
      (CFSG.Quasithin.twoPrimeResidual
        ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D u))) : Set D) := by
    have := CFSG.Quasithin.le_normalizer_conjClosure (R.U.map (littleGroup D Γ n).subtype)
      ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D u)))
    rwa [CFSG.Quasithin.conjClosure_eq_twoPrimeResidual hUK] at this
  have hU_le_N : (R.U.map (littleGroup D Γ n).subtype) ≤
      CFSG.Quasithin.twoPrimeResidual ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D u))) := by
    have := CFSG.Quasithin.le_conjClosure (R.U.map (littleGroup D Γ n).subtype)
      ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D u)))
    rwa [CFSG.Quasithin.conjClosure_eq_twoPrimeResidual hUK] at this
  have hN_le : CFSG.Quasithin.twoPrimeResidual
      ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D u))) ≤
        (littleGroup D Γ n) ⊓ ((MulAction.stabilizer D u)) := by
    rw [CFSG.Quasithin.twoPrimeResidual]
    exact iInf₂_le _ ⟨le_rfl, Subgroup.le_normalizer, by simp⟩
  have hnormW1 : ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D u))) ⊓
      Subgroup.normalizer ((R.U.map (littleGroup D Γ n).subtype) : Set D) ≤ ψ₁.range := by
    intro x hx
    have hxM : x ∈ ((R.B.map (littleGroup D Γ n).subtype)) := by
      have h : x ∈ Subgroup.normalizer ((R.U.map (littleGroup D Γ n).subtype) : Set D) ⊓
          (littleGroup D Γ n) := ⟨hx.2, hx.1.1⟩
      rwa [hNormU] at h
    exact hBψ_le_ψ₁ (hM_le_Bψ hxM)
  have hK1_ψ : (littleGroup D Γ n) ⊓ ((MulAction.stabilizer D u)) ≤ ψ₁.range :=
    le_of_residual_le hU_le_N hN_le hK_le_norm hUK
      (twoPrimeResidual_le (K := (littleGroup D Γ n) ⊓ ((MulAction.stabilizer D u)))
        (W := ψ₁.range) step2) hnormW1
  have hK_le_norm_v : (littleGroup D Γ n) ⊓ ((MulAction.stabilizer D v)) ≤ Subgroup.normalizer
      (CFSG.Quasithin.twoPrimeResidual
        ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D v))) : Set D) := by
    have := CFSG.Quasithin.le_normalizer_conjClosure (R.U.map (littleGroup D Γ n).subtype)
      ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D v)))
    rwa [CFSG.Quasithin.conjClosure_eq_twoPrimeResidual hUKv] at this
  have hU_le_Nv : (R.U.map (littleGroup D Γ n).subtype) ≤
      CFSG.Quasithin.twoPrimeResidual ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D v))) := by
    have := CFSG.Quasithin.le_conjClosure (R.U.map (littleGroup D Γ n).subtype)
      ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D v)))
    rwa [CFSG.Quasithin.conjClosure_eq_twoPrimeResidual hUKv] at this
  have hN_le_v : CFSG.Quasithin.twoPrimeResidual
      ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D v))) ≤
        (littleGroup D Γ n) ⊓ ((MulAction.stabilizer D v)) := by
    rw [CFSG.Quasithin.twoPrimeResidual]
    exact iInf₂_le _ ⟨le_rfl, Subgroup.le_normalizer, by simp⟩
  have hnormW2 : ((littleGroup D Γ n) ⊓ ((MulAction.stabilizer D v))) ⊓
      Subgroup.normalizer ((R.U.map (littleGroup D Γ n).subtype) : Set D) ≤ ψ₂.range := by
    intro x hx
    have hxM : x ∈ ((R.B.map (littleGroup D Γ n).subtype)) := by
      have h : x ∈ Subgroup.normalizer ((R.U.map (littleGroup D Γ n).subtype) : Set D) ⊓
          (littleGroup D Γ n) := ⟨hx.2, hx.1.1⟩
      rwa [hNormU] at h
    exact hBψ_le_ψ₂ (hM_le_Bψ hxM)
  have hK2_ψ : (littleGroup D Γ n) ⊓ ((MulAction.stabilizer D v)) ≤ ψ₂.range :=
    le_of_residual_le hU_le_Nv hN_le_v hK_le_norm_v hUKv
      (twoPrimeResidual_le (K := (littleGroup D Γ n) ⊓ ((MulAction.stabilizer D v)))
        (W := ψ₂.range) step2v) hnormW2
  have hψ₁_le : ψ₁.range ≤ (littleGroup D Γ n) ⊔ ((psiB P2 ψ₁).range) := by
    intro x hx
    have hxDu : x ∈ ((MulAction.stabilizer D u)) := hψ₁u hx
    have hxuv : x • u = u := (hmemDu x).mp hxDu
    have hadj : Γ.Adj u (x • v) := by
      have h := (GraphAction.adj_smul x u v).mpr huv
      rwa [hxuv] at h
    obtain ⟨l, hlL, hlu, hlv⟩ :=
      littleGroup_stabilizer_transitive hn hpoly hthick hmouf hadj huv
    have hlDu : l ∈ ((MulAction.stabilizer D u)) := (hmemDu l).mpr hlu
    have hlψ : l ∈ ψ₁.range := hK1_ψ ⟨hlL, hlDu⟩
    have hlxψ : l * x ∈ ψ₁.range := ψ₁.range.mul_mem hlψ hx
    have hlxdv : l * x ∈ ((MulAction.stabilizer D v)) := by
      rw [hmemDv, mul_smul, hlv]
    have hlxB : l * x ∈ ((psiB P2 ψ₁).range) := by rw [← hint1]; exact ⟨hlxψ, hlxdv⟩
    have hx_eq : x = l⁻¹ * (l * x) := by group
    rw [hx_eq]
    exact Subgroup.mul_mem_sup ((littleGroup D Γ n).inv_mem hlL) hlxB
  have hψ₂_le : ψ₂.range ≤ (littleGroup D Γ n) ⊔ ((psiB P2 ψ₁).range) := by
    intro x hx
    have hxDv : x ∈ ((MulAction.stabilizer D v)) := hψ₂v hx
    have hxvu : x • v = v := (hmemDv x).mp hxDv
    have hadj : Γ.Adj v (x • u) := by
      have h := (GraphAction.adj_smul x v u).mpr huve
      rwa [hxvu] at h
    obtain ⟨l, hlL, hlv, hlu⟩ :=
      littleGroup_stabilizer_transitive hn hpoly hthick hmouf hadj huve
    have hlDv : l ∈ ((MulAction.stabilizer D v)) := (hmemDv l).mpr hlv
    have hlψ : l ∈ ψ₂.range := hK2_ψ ⟨hlL, hlDv⟩
    have hlxψ : l * x ∈ ψ₂.range := ψ₂.range.mul_mem hlψ hx
    have hlxdu : l * x ∈ ((MulAction.stabilizer D u)) := by
      rw [hmemDu, mul_smul, hlu]
    have hlxB : l * x ∈ ((psiB P2 ψ₁).range) := by rw [← hint2]; exact ⟨hlxψ, hlxdu⟩
    have hx_eq : x = l⁻¹ * (l * x) := by group
    rw [hx_eq]
    exact Subgroup.mul_mem_sup ((littleGroup D Γ n).inv_mem hlL) hlxB
  have hD_eq : (littleGroup D Γ n) ⊔ ((psiB P2 ψ₁).range) = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = ψ₁.range ⊔ ψ₂.range := hgen.symm
      _ ≤ (littleGroup D Γ n) ⊔ ((psiB P2 ψ₁).range) := sup_le hψ₁_le hψ₂_le
  have hDu_le : ((MulAction.stabilizer D u)) ≤ ψ₁.range := by
    intro d hd
    obtain ⟨l, hl, b, hb, hlb⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := (littleGroup D Γ n))
        (t := ((psiB P2 ψ₁).range))).mp (hD_eq ▸ Subgroup.mem_top d)
    have hlDu : l ∈ ((MulAction.stabilizer D u)) := by
      have h : l = d * b⁻¹ := by rw [← hlb]; group
      rw [h]
      exact ((MulAction.stabilizer D u)).mul_mem hd
        (((MulAction.stabilizer D u)).inv_mem (hBψ_le_Du hb))
    rw [← hlb]
    exact ψ₁.range.mul_mem (hK1_ψ ⟨hl, hlDu⟩) (hBψ_le_ψ₁ hb)
  have hDv_le : ((MulAction.stabilizer D v)) ≤ ψ₂.range := by
    intro d hd
    obtain ⟨l, hl, b, hb, hlb⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := (littleGroup D Γ n))
        (t := ((psiB P2 ψ₁).range))).mp (hD_eq ▸ Subgroup.mem_top d)
    have hlDv : l ∈ ((MulAction.stabilizer D v)) := by
      have h : l = d * b⁻¹ := by rw [← hlb]; group
      rw [h]
      exact ((MulAction.stabilizer D v)).mul_mem hd
        (((MulAction.stabilizer D v)).inv_mem (hBψ_le_Dv hb))
    rw [← hlb]
    exact ψ₂.range.mul_mem (hK2_ψ ⟨hl, hlDv⟩) (hBψ_le_ψ₂ hb)
  refine ⟨le_antisymm hψ₁u hDu_le, le_antisymm hψ₂v hDv_le, ?_⟩
  refine le_antisymm (le_inf hBψ_le_Du hBψ_le_Dv) ?_
  rw [← hint1]
  exact le_inf (inf_le_left.trans hDu_le) inf_le_right


end CFSG.Quasithin.Stroth
