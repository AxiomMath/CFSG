module

public import CFSG.Quasithin.Vol2.Ch7Sec77Mod
public import CFSG.Quasithin.Background.HU33Sq
public import CFSG.Quasithin.EmptyFaithful.ModDGlue

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem wordProd_u33GenPG : ∀ w : List (Fin 5 × Bool),
    CFSG.Sporadic.Bridge.wordProd u33GenPG (w.map fun l => (l.1.val, l.2)) = ModD.gOfWord w
  | [] => rfl
  | l :: w => by
    have ih := wordProd_u33GenPG w
    unfold CFSG.Sporadic.Bridge.wordProd ModD.gOfWord at ih ⊢
    simp only [List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    congr 1
    rcases l with ⟨i, b⟩
    cases b <;> simp [u33GenPG_of]

theorem vHom_tel
    (j : Fin 32) : ModD.vHom (u33Data.Tel j) = U33Sq.telP j := by
  show ModD.vHom (u33Tel u33GenPG j.val) = _
  rw [u33Tel, u33TelW, u33W, wordProd_u33GenPG,
    ModD.hom_gOfWord ModD.vHom ModD.vImg ModD.vHom_of]
  rfl

theorem card_le_four_of_fix_sq
    {U : Type} [CommGroup U] [Finite U] (hsq : ∀ a : U, a * a = 1)
    (φ : U33G →* MulAut U) (Z : Subgroup U) (hZ : ∀ g : U33G, ∀ ζ ∈ Z, φ g ζ = ζ)
    (hcard : Nat.card (U ⧸ Z) = 2 ^ 6)
    (hirr : ∀ N : Subgroup U, Z ≤ N → (∀ g : U33G, ∀ n ∈ N, φ g n ∈ N) → N = Z ∨ N = ⊤)
    {W : Subgroup U} (hWZ : W ⊓ Z = ⊥) (hW : ∀ t ∈ u33Data.T, ∀ w ∈ W, φ (t * t) w = w) :
    Nat.card W ≤ 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ' : U33G →* MulAut (U ⧸ Z) := ModD.actQ φ Z hZ
  have hφ' : ∀ g x, φ' g (QuotientGroup.mk x) = QuotientGroup.mk (φ g x) := fun g x =>
    ModD.actQ_mk φ Z hZ g x
  have hsq' : ∀ a : U ⧸ Z, a * a = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul, hsq x]
      rfl
  have hirr' : ∀ N : Subgroup (U ⧸ Z), (∀ g : U33G, ∀ n ∈ N, φ' g n ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    let N' : Subgroup U := N.comap (QuotientGroup.mk' Z)
    have hZN : Z ≤ N' := by
      intro x hx
      show (QuotientGroup.mk x : U ⧸ Z) ∈ N
      rw [(QuotientGroup.eq_one_iff x).2 hx]
      exact N.one_mem
    have hinv : ∀ g : U33G, ∀ n ∈ N', φ g n ∈ N' := by
      intro g n hn
      show (QuotientGroup.mk (φ g n) : U ⧸ Z) ∈ N
      rw [← hφ']
      exact hN g _ hn
    rcases hirr N' hZN hinv with h | h
    · left
      refine eq_bot_iff.2 fun x hx => ?_
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      have hu : u ∈ N' := hx
      rw [h] at hu
      exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff u).2 hu)
    · right
      refine eq_top_iff.2 fun x _ => ?_
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      have hu : u ∈ N' := by rw [h]; trivial
      exact hu
  obtain ⟨z, hz1, hzT⟩ : ∃ z : U ⧸ Z, z ≠ 1 ∧ ∀ g ∈ u33Data.T, φ' g z = z := by
    let ψT : ↥u33Data.T →* MulAut (U ⧸ Z) := φ'.comp u33Data.T.subtype
    let _ : MulAction ↥u33Data.T (U ⧸ Z) := MulAction.compHom (U ⧸ Z) ψT
    have hmod := u33_syl.1.card_modEq_card_fixedPoints (U ⧸ Z)
    rw [hcard] at hmod
    by_contra hcon
    push Not at hcon
    have hsub : MulAction.fixedPoints ↥u33Data.T (U ⧸ Z) ⊆ {1} := by
      intro x hx
      by_contra hx1
      obtain ⟨g, hg, hgx⟩ := hcon x hx1
      exact hgx (hx ⟨g, hg⟩)
    have h1 : (1 : U ⧸ Z) ∈ MulAction.fixedPoints ↥u33Data.T (U ⧸ Z) := fun g => by
      show (ψT g) 1 = 1
      exact map_one _
    have heq : MulAction.fixedPoints ↥u33Data.T (U ⧸ Z) = {1} :=
      Set.eq_of_subset_of_subset hsub (Set.singleton_subset_iff.mpr h1)
    rw [heq, Nat.card_unique] at hmod
    exact absurd hmod (by decide)
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hsq' z
  have hstab := ModD.stab_eq_A hcard φ' hirr' hz1 hz2 hzT
  have hst : ∀ g, φ' g z = z ↔ ModD.vHom g 0 = 0 := by
    intro g
    have h : g ∈ ModD.stabSub φ' z ↔ g ∈ ModD.stabπ ModD.vHom := by rw [hstab, ModD.stab_vHom]
    exact h.trans ModD.mem_stabπ
  obtain ⟨ε, hε1, hε2, hε3⟩ := ModD.exists_label φ' z ModD.vHom 0 hst
  have hsurj : ∀ j, ∃ g, ε (φ' g z) = j := fun j => by
    obtain ⟨g, hg⟩ := ModD.vHom_trans j
    exact ⟨g, by rw [hε1]; exact hg⟩
  have horb := ModD.orbit_eq_ne_one φ' hz1 (by rw [hcard]; simp) ε hε2 hsurj
  have hmk1 : ∀ w ∈ W, w ≠ 1 → (QuotientGroup.mk w : U ⧸ Z) ≠ 1 := by
    intro w hw hw1 h
    have h1 : w ∈ W ⊓ Z := ⟨hw, (QuotientGroup.eq_one_iff w).1 h⟩
    rw [hWZ] at h1
    exact hw1 h1
  set S3 := Finset.univ.filter fun i : Fin 63 => ∀ j : Fin 32, (U33Sq.telP j * U33Sq.telP j) i = i
    with hS3def
  have hmap : ∀ w ∈ W, w ≠ 1 → ε (QuotientGroup.mk w) ∈ S3 := by
    intro w hw hw1
    have hmo := horb _ (hmk1 w hw hw1)
    rw [hS3def, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun j => ?_⟩
    have hT : u33Data.Tel j ∈ u33Data.T := (u33Data.mem_T_iff _).2 ⟨j, rfl⟩
    have h1 : φ' (u33Data.Tel j * u33Data.Tel j) (QuotientGroup.mk w) = QuotientGroup.mk w := by
      rw [hφ', hW _ hT w hw]
    have h2 := hε3 (u33Data.Tel j * u33Data.Tel j) _ hmo
    rw [h1, map_mul, vHom_tel] at h2
    exact h2.symm
  let _ : Fintype ↥W := Fintype.ofFinite _
  have hcount : (Finset.univ.filter fun w : ↥W => w ≠ 1).card ≤ S3.card := by
    refine Finset.card_le_card_of_injOn (fun w => ε (QuotientGroup.mk (w : U))) ?_ ?_
    · intro w hw
      have hw1 : (w : U) ≠ 1 := fun h => (Finset.mem_filter.1 hw).2 (Subtype.ext h)
      exact hmap w w.2 hw1
    · intro a ha b hb hab
      have ha1 : (a : U) ≠ 1 := fun h => (Finset.mem_filter.1 ha).2 (Subtype.ext h)
      have hb1 : (b : U) ≠ 1 := fun h => (Finset.mem_filter.1 hb).2 (Subtype.ext h)
      have h1 := hε2 _ _ (horb _ (hmk1 a a.2 ha1)) (horb _ (hmk1 b b.2 hb1)) hab
      have h2 : (a : U)⁻¹ * b ∈ Z := QuotientGroup.eq.1 h1
      have h3 : (a : U)⁻¹ * b ∈ W ⊓ Z := ⟨W.mul_mem (W.inv_mem a.2) b.2, h2⟩
      rw [hWZ, Subgroup.mem_bot, inv_mul_eq_one] at h3
      exact Subtype.ext h3
  have hS3 : S3.card = 3 := U33Sq.card_fix_sq
  have hfilt : (Finset.univ.filter fun w : ↥W => w ≠ 1).card = Nat.card W - 1 := by
    rw [Finset.filter_ne' Finset.univ (1 : ↥W), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Nat.card_eq_fintype_card]
  have hpos : 0 < Nat.card W := Nat.card_pos
  omega

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem false_of_g2Block
    (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hG2 : CFSG.Quasithin.IsG2Block K) {r b : ℕ} (hr : ¬ 3 ∣ r) (hyK : θ ^ r ∈ K)
    (hyb : orderOf (θ ^ r) = 3 ^ b) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := C.conf.hc
  have hshort : IsShort2 K := hG2.1
  have hyM : θ ^ r ∈ fsuM T L := (fsuM T L).pow_mem (S.L_le_fsuM hc.mem) r
  have hyo : Odd (orderOf (θ ^ r)) := by rw [hyb]; exact Odd.pow (by decide)
  obtain ⟨hvmU, hvmZ⟩ := C.vm_le_blockU hF hK hyK hyM hyo (pow_not_mem hc hr)
  set X := T ⊓ Subgroup.centralizer (Vp : Set G) ⊓ K with hXdef
  have hXS : IsSylowTwoOf X K :=
    CFSG.Quasithin.A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK) C.conf.sylH
  obtain ⟨R, hRX, hR2, hRQ⟩ := C.exists_index_two_Q (inf_le_left : X ≤ _)
  have hsqR : ∀ x ∈ X, x * x ∈ R := by
    intro x hx
    set B := R.subgroupOf X with hB
    have hBi : B.index ≤ 2 := hR2
    have hB0 : B.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hxB : (⟨x, hx⟩ : ↥X) * ⟨x, hx⟩ ∈ B := by
      interval_cases hi : B.index
      · exact absurd rfl hB0
      · rw [Subgroup.index_eq_one] at hi
        rw [hi]
        exact Subgroup.mem_top _
      · have := Subgroup.normal_of_index_eq_two hi
        have h1 := Subgroup.pow_index_mem B (⟨x, hx⟩ : ↥X)
        rw [hi, pow_two] at h1
        exact h1
    exact Subgroup.mem_subgroupOf.mp hxB
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.mp hXS
  have hPX : ∀ k : ↥K, k ∈ (P : Subgroup ↥K) → (k : G) ∈ X := fun k hk => by
    rw [← hP]
    exact ⟨k, hk, rfl⟩
  obtain ⟨ψ, hψs, hψk, hψP⟩ := ModD.exists_psi hG2.2.1 P
  obtain ⟨φ, hφ⟩ := ModD.exists_phi hshort ψ hψs hψk
  have hsqU : ∀ w : ↥(blockU K), w ^ 2 = 1 := fun w => Subtype.ext (hshort.2.2.1.2 w w.2)
  have hcomm : IsMulCommutative ↥(blockU K) :=
    IsMulCommutative.of_comm fun a b => Subtype.ext
      (C1.blockU_comm hshort a.1 a.2 b.1 (C1.blockU_le_blockQ hshort b.2))
  have hsq : ∀ a : ↥(blockU K), a * a = 1 := fun a => by rw [← pow_two]; exact hsqU a
  have hZU : blockZ K ≤ blockU K := inf_le_left
  let Z' : Subgroup ↥(blockU K) := (blockZ K).subgroupOf (blockU K)
  have hcardU : Nat.card (↥(blockU K) ⧸ Z') = 2 ^ 6 := hG2.2.2.1
  have hZfix : ∀ g : U33G, ∀ ζ ∈ Z', φ g ζ = ζ := by
    intro g ζ hζ
    obtain ⟨k, rfl⟩ := hψs g
    apply Subtype.ext
    rw [hφ]
    have hζc : (ζ : G) ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_subgroupOf.1 hζ).2
    have h1 := Subgroup.mem_centralizer_iff.1 hζc (k : G) k.2
    show (k : G) * (ζ : G) * (k : G)⁻¹ = (ζ : G)
    rw [h1, mul_inv_cancel_right]
  have hirr : ∀ N : Subgroup ↥(blockU K), Z' ≤ N → (∀ g : U33G, ∀ n ∈ N, φ g n ∈ N) →
      N = Z' ∨ N = ⊤ := by
    intro N hZN hN
    have hfwd : ∀ k ∈ K, ∀ h ∈ N.map (blockU K).subtype,
        k * h * k⁻¹ ∈ N.map (blockU K).subtype := by
      intro k hk h hh
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hh
      refine Subgroup.mem_map.2 ⟨φ (ψ ⟨k, hk⟩) n, hN _ n hn, ?_⟩
      exact hφ ⟨k, hk⟩ n
    have hnorm : K ≤ Subgroup.normalizer ((N.map (blockU K).subtype : Subgroup G) : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨hfwd k hk h, fun hh => ?_⟩
      have h1 := hfwd k⁻¹ (K.inv_mem hk) _ hh
      have e : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
      rwa [e] at h1
    have hZW : blockZ K ≤ N.map (blockU K).subtype := by
      intro x hx
      exact Subgroup.mem_map.2 ⟨⟨x, hZU hx⟩, hZN (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    rcases hshort.2.2.2.2.2 (N.map (blockU K).subtype) hZW
      (Subgroup.map_subtype_le N) hnorm with h | h
    · left
      apply Subgroup.map_injective (blockU K).subtype_injective
      rw [h]
      exact (Subgroup.map_subgroupOf_eq_of_le hZU).symm
    · right
      apply Subgroup.map_injective (blockU K).subtype_injective
      rw [h, Subgroup.map_top, Subgroup.range_subtype]
  let W : Subgroup ↥(blockU K) := (S.vm e).subgroupOf (blockU K)
  have hWcard : Nat.card W = 16 := by
    rw [show Nat.card W = Nat.card (S.vm e) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hvmU).toEquiv, card_vm]
  have hWZ : W ⊓ Z' = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have h1 : (w : G) ∈ S.vm e ⊓ blockZ K :=
      ⟨Subgroup.mem_subgroupOf.1 hw.1, Subgroup.mem_subgroupOf.1 hw.2⟩
    rw [hvmZ, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  have hWfix : ∀ t ∈ u33Data.T, ∀ w ∈ W, φ (t * t) w = w := by
    intro t ht w hw
    rw [← hψP] at ht
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 ht
    have hpp : (p : G) * p ∈ T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
      hRQ (hsqR _ (hPX p hp))
    rw [← map_mul]
    apply Subtype.ext
    rw [hφ]
    have h1 := Subgroup.mem_centralizer_iff.mp hpp.2 (w : G)
      (vm_le (Subgroup.mem_subgroupOf.1 hw))
    show ((p * p : ↥K) : G) * w * ((p * p : ↥K) : G)⁻¹ = w
    rw [Subgroup.coe_mul, ← h1, mul_inv_cancel_right]
  have h4 := card_le_four_of_fix_sq hsq φ Z' hZfix hcardU hirr hWZ hWfix
  omega

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
