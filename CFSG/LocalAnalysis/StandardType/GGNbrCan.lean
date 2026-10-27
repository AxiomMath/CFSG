module

public import CFSG.LocalAnalysis.StandardType.GGNbrCentralizer
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggNbr_mem_normalizer_of_card_inf {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hcard : p ^ 3 ≤ Nat.card ↥(Bs ⊓ K)) {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgy : g ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G)) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hK : IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hH.1.1.2.2.2.2.2.2.2
      (isNeighborOf_of_ggNbr hH.1.2.2 hnb)).1
  exact normalizer_inf_le_of_card_lt hK
    ((card_bstar_inf_centralizer_le hH.1 hnb).trans_lt
      ((Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num : 2 < 3)).trans_le hcard))
    ⟨hg, hgy⟩

private theorem l05nQ2_rawDatum_elim_const {lab : LargeEvenLabel} {Q : Prop}
    (h : LargeEvenRawDatum lab (fun (R : Type) [Group R] _ _ => Q)) : Q := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h; exact hq)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h; exact hq)

private theorem l05nQ2_marking_elim_const {X : Type*} [Group X] {Q : Prop}
    (h : LargeEvenMarking X (fun _ _ _ _ _ _ => Q)) : Q := by
  obtain ⟨-, lab, -, hraw⟩ := h
  exact l05nQ2_rawDatum_elim_const
    (largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨-, -, -, hθ⟩ := hq
      exact hθ) hraw)

private theorem l05nQ2_le_normalizer_of_innerDiagOn {G : Type} [Group G] {Bs X : Subgroup G}
    (h : GGInnerDiagOn Bs X) : Bs ≤ Subgroup.normalizer (X : Set G) :=
  l05nQ2_marking_elim_const (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) h)

private theorem l05nQ2_y_ne_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : y ≠ 1 := by
  intro hy1
  have hp : p.Prime := Fact.out
  have hpre := hH.1.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDea := hpre.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hDgen : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hxp : x ^ p = 1 := hDea.2 x hxD
  have hDle : D ≤ Subgroup.zpowers x := by
    rw [hDgen, hy1, Subgroup.closure_le]
    intro a ha
    have ha' : a = x ∨ a = 1 := by simpa using ha
    rcases ha' with h | h
    · rw [h]; exact Subgroup.mem_zpowers x
    · rw [h]; exact Subgroup.one_mem _
  have hxle : Nat.card (Subgroup.zpowers x) ≤ p := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hxp
  have hcon : p ^ 2 ≤ p := by
    calc p ^ 2 = Nat.card D := hDcard.symm
      _ ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hDle
      _ ≤ p := hxle
  nlinarith [hcon, hp.two_le]

private theorem l05nQ2_aut_eq_one_or_transvection {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs : Subgroup G} {y : G} (hyBs : y ∈ Bs) (hy1 : y ≠ 1)
    (hBs : CFSG.Open.IsElemAbelian p Bs) {ψ : MulAut ↥Bs}
    (hψy : ψ ⟨y, hyBs⟩ = ⟨y, hyBs⟩)
    (hψ : ∀ b : ↥Bs, ((b⁻¹ * ψ b : ↥Bs) : G) ∈ Subgroup.zpowers y) :
    ψ = 1 ∨ GGIsTransvection p ψ := by
  classical
  haveI : IsMulCommutative ↥Bs := hBs.1
  let c : ↥Bs := ⟨y, hyBs⟩
  have hψc : ψ c = c := by simpa only [c] using hψy
  have hcp : c ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (y : G) ^ p = 1
    exact hBs.2 y hyBs
  have hc1 : c ≠ 1 := by
    intro h
    exact hy1 (by simpa [c] using congrArg Subtype.val h)
  have hc_ord : orderOf c = p := orderOf_eq_prime hcp hc1
  let D : ↥Bs →* ↥Bs :=
    { toFun := fun b => b⁻¹ * ψ b
      map_one' := by simp
      map_mul' := by
        intro a b
        show (a * b)⁻¹ * ψ (a * b) = (a⁻¹ * ψ a) * (b⁻¹ * ψ b)
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  have hD_apply : ∀ b : ↥Bs, D b = b⁻¹ * ψ b := fun b => rfl
  have hfix : ∀ b : ↥Bs, ψ (b⁻¹ * ψ b) = b⁻¹ * ψ b := by
    intro b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hψ b)
    have hck : c ^ k = b⁻¹ * ψ b := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      change (y : G) ^ k = ((b⁻¹ * ψ b : ↥Bs) : G)
      exact hk
    calc ψ (b⁻¹ * ψ b) = ψ (c ^ k) := by rw [hck]
      _ = (ψ c) ^ k := map_zpow ψ c k
      _ = c ^ k := by rw [hψc]
      _ = b⁻¹ * ψ b := hck
  have hD_ker : Nat.card {b : ↥Bs // ψ b = b} = Nat.card D.ker := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun b => ?_)
    show ψ b = b ↔ b ∈ D.ker
    rw [MonoidHom.mem_ker, hD_apply]
    exact eq_comm.trans inv_mul_eq_one.symm
  have hD_range_le : D.range ≤ Subgroup.zpowers c := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_zpowers_iff]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hψ b)
    refine ⟨k, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    change (y : G) ^ k = ((b⁻¹ * ψ b : ↥Bs) : G)
    exact hk
  have hcard_zp : Nat.card (Subgroup.zpowers c) = p := by
    rw [Nat.card_zpowers, hc_ord]
  have hcardD : Nat.card D.ker * Nat.card D.range = Nat.card ↥Bs :=
    Subgroup.card_ker_mul_card_range D
  have hdvd : Nat.card D.range ∣ p := by
    have h := Subgroup.card_dvd_of_le hD_range_le
    rwa [hcard_zp] at h
  by_cases hψ1 : ψ = 1
  · exact Or.inl hψ1
  · right
    refine ⟨?_, hfix⟩
    rw [hD_ker]
    rcases Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) (Nat.card D.range) hdvd with
      h1 | hpeq
    · exfalso
      have hbot : D.range = ⊥ := Subgroup.eq_bot_of_card_eq D.range h1
      have hD1 : D = 1 := by
        ext b
        have hmem : D b ∈ D.range := MonoidHom.mem_range.mpr ⟨b, rfl⟩
        rw [hbot] at hmem
        simpa using hmem
      apply hψ1
      ext b
      have hb : D b = 1 := by rw [hD1]; rfl
      have hb' : b⁻¹ * ψ b = 1 := by rw [← hD_apply]; exact hb
      exact congrArg Subtype.val (inv_mul_eq_one.mp hb').symm
    · rw [hpeq] at hcardD
      exact hcardD

theorem ggNbr_mem_normalizer {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y)
    (hnt : ggAutomizer K Bs ≠ ⊥) {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (hgy : g * y * g⁻¹ = y) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  have hst : LargeEvenStandardType p B x L := hH.1.1.2.2.2.2.2.2.2
  have hDJ : LargeEvenStdSub p B x L D J := hH.1.2.2
  have hNbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hcompK : IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ hNbr)).1
  have hBsNormK : Bs ≤ Subgroup.normalizer (K : Set G) :=
    l05nQ2_le_normalizer_of_innerDiagOn (hH.2.2.1.2 y K hNbr)
  have hgy' : g * y = y * g := by
    calc g * y = (g * y * g⁻¹) * g := by group
      _ = y * g := by rw [hgy]
  have hCy : (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({y} : Set G) :=
    centralizer_map_conj_of_commute hgy'
  have hcompK' : IsComponentOf (K.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer ({y} : Set G)) := by
    have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcompK g
    rwa [hCy] at h1
  have hBsNormK' : Bs ≤ Subgroup.normalizer
      ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    intro b hb
    rw [mem_normalizer_iff_map_conj]
    have hgb : g⁻¹ * b * g ∈ Bs := (Subgroup.mem_normalizer_iff''.mp hg b).mp hb
    have hK'' : K.map (MulAut.conj (g⁻¹ * b * g)).toMonoidHom = K :=
      mem_normalizer_iff_map_conj.mp (hBsNormK hgb)
    calc (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj b).toMonoidHom
        = K.map (MulAut.conj (b * g)).toMonoidHom := map_conj_map_conj K g b
      _ = K.map (MulAut.conj (g * (g⁻¹ * b * g))).toMonoidHom := by
            rw [show b * g = g * (g⁻¹ * b * g) by group]
      _ = (K.map (MulAut.conj (g⁻¹ * b * g)).toMonoidHom).map
            (MulAut.conj g).toMonoidHom := (map_conj_map_conj K (g⁻¹ * b * g) g).symm
      _ = K.map (MulAut.conj g).toMonoidHom := by rw [hK'']
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hcompK' hcompK with
    hEq | hComm
  · exact mem_normalizer_iff_map_conj.mpr hEq
  · exfalso
    have hK'cent : K.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.centralizer (K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hComm
    have hex : ∃ φ ∈ ggInduced K Bs, φ ≠ 1 := by
      by_contra h
      push Not at h
      apply hnt
      rw [ggAutomizer]
      apply le_antisymm _ bot_le
      rw [Subgroup.closure_le]
      intro φ hφ
      simpa using h φ hφ
    obtain ⟨ν₀, hν₀mem, hν₀ne⟩ := hex
    simp only [ggInduced, Set.mem_setOf_eq] at hν₀mem
    obtain ⟨n₀, hn₀K, hn₀N, hn₀act⟩ := hν₀mem
    set n : G := g * n₀ * g⁻¹ with hn_def
    have hnK' : n ∈ K.map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.mem_map]
      exact ⟨n₀, hn₀K, by rw [hn_def]; rfl⟩
    have hnN : n ∈ Subgroup.normalizer (Bs : Set G) := by
      rw [hn_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hn₀N) (Subgroup.inv_mem _ hg)
    have hny : n * y * n⁻¹ = y := by
      have hcomm : n * y = y * n :=
        Subgroup.mem_centralizer_singleton_iff.mp (hcompK'.1 hnK')
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    let cg : MulAut ↥Bs := Bs.normalizerMonoidHom ⟨g, hg⟩
    let ν : MulAut ↥Bs := cg * ν₀ * cg⁻¹
    have hcg : ∀ a : ↥Bs, ((cg a : ↥Bs) : G) = g * a * g⁻¹ :=
      fun a => Subgroup.normalizerMonoidHom_apply_apply_coe Bs ⟨g, hg⟩ a
    have hcgi : ∀ a : ↥Bs, ((cg⁻¹ a : ↥Bs) : G) = g⁻¹ * a * g := by
      intro a
      have hsymm : cg⁻¹ = MulEquiv.symm cg := rfl
      rw [hsymm]
      exact Subgroup.normalizerMonoidHom_apply_symm_apply_coe Bs ⟨g, hg⟩ a
    have hνne : ν ≠ 1 := by
      intro hν1
      apply hν₀ne
      have hνdef : ν = cg * ν₀ * cg⁻¹ := rfl
      have hconj : cg⁻¹ * ν * cg = ν₀ := by rw [hνdef]; group
      rw [hν1] at hconj
      simpa using hconj.symm
    have hνact : ∀ b : ↥Bs, ((ν b : ↥Bs) : G) = n * b * n⁻¹ := by
      intro b
      have hνdef : ν = cg * ν₀ * cg⁻¹ := rfl
      calc ((ν b : ↥Bs) : G)
          = ((cg (ν₀ (cg⁻¹ b)) : ↥Bs) : G) := by rw [hνdef]; rfl
        _ = g * ((ν₀ (cg⁻¹ b) : ↥Bs) : G) * g⁻¹ := hcg _
        _ = g * (n₀ * ((cg⁻¹ b : ↥Bs) : G) * n₀⁻¹) * g⁻¹ := by rw [hn₀act]
        _ = g * (n₀ * (g⁻¹ * (b : G) * g) * n₀⁻¹) * g⁻¹ := by rw [hcgi b]
        _ = (g * n₀ * g⁻¹) * (b : G) * (g * n₀ * g⁻¹)⁻¹ := by group
        _ = n * (b : G) * n⁻¹ := by rw [hn_def]
    have hνmem : ν ∈ ggInduced ⊤ Bs := by
      simp only [ggInduced, Set.mem_setOf_eq]
      exact ⟨n, Subgroup.mem_top n, hnN, hνact⟩
    have hνmove : ∀ b : ↥Bs, ((b⁻¹ * ν b : ↥Bs) : G) ∈ Subgroup.zpowers y := by
      intro b
      have hbK' : (b : G)⁻¹ * n * (b : G) ∈ K.map (MulAut.conj g).toMonoidHom :=
        (Subgroup.mem_normalizer_iff''.mp (hBsNormK' b.2) n).mp hnK'
      have hDmemK' : ((b⁻¹ * ν b : ↥Bs) : G) ∈ K.map (MulAut.conj g).toMonoidHom := by
        have h2 : (b : G)⁻¹ * n * (b : G) * n⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom :=
          Subgroup.mul_mem _ hbK' (Subgroup.inv_mem _ hnK')
        have hcoe : ((b⁻¹ * ν b : ↥Bs) : G) = (b : G)⁻¹ * n * (b : G) * n⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hνact b]
          group
        rw [hcoe]; exact h2
      have hmem : ((b⁻¹ * ν b : ↥Bs) : G) ∈
          Bs ⊓ Subgroup.centralizer (K : Set G) :=
        ⟨(b⁻¹ * ν b).2, hK'cent hDmemK'⟩
      rw [ggNbr_inf_centralizer hH hCent] at hmem
      exact hmem
    have hyBs : y ∈ Bs := hH.1.2.1.1 hNbr.1.2.1
    have hy1 : y ≠ 1 := l05nQ2_y_ne_one hH
    have hνy : ν ⟨y, hyBs⟩ = ⟨y, hyBs⟩ := by
      apply Subtype.ext
      rw [hνact ⟨y, hyBs⟩]
      exact hny
    have htrans : GGIsTransvection p ν :=
      (l05nQ2_aut_eq_one_or_transvection hyBs hy1 hH.1.2.1.2.1 hνy hνmove).resolve_left hνne
    exact hH.2.2.2.1 ν hνmem htrans

end CFSG.StandardType
