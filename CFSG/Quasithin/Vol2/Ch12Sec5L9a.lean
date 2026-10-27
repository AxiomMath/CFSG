module

public import CFSG.Quasithin.Vol2.Ch12Sec5L7
public import CFSG.Quasithin.Vol2.Ch12Sec5L5c
public import CFSG.Quasithin.Vol2.Ch12Sec5L2
public import CFSG.Quasithin.Background.E6TwentySeven
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St Matrix
open scoped IsMulCommutative

namespace S125L9a

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem card_of_isSylowTwoOf {S H : Subgroup G} (hS : QuasithinUnique.IsSylowTwoOf S H) {a m : ℕ}
    (hH : Nat.card H = 2 ^ a * m) (hm : ¬ 2 ∣ m) : Nat.card S = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  have h1 : S.relIndex H * Nat.card S = Nat.card H := by
    have := Subgroup.relIndex_mul_card (H := S) (K := H)
    rwa [inf_of_le_left hS.1] at this
  have hodd : ¬ 2 ∣ S.relIndex H := hS.2.2
  rw [hH, hk] at h1
  rw [hk]
  generalize S.relIndex H = i at h1 hodd
  have hk1 : k ≤ a := by
    have hd : 2 ^ k ∣ 2 ^ a * m := ⟨i, by rw [← h1, mul_comm]⟩
    have hc : Nat.Coprime (2 ^ k) m :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hc.dvd_of_dvd_mul_right hd)
  have hk2 : a ≤ k := by
    have hd : 2 ^ a ∣ i * 2 ^ k := ⟨m, h1⟩
    have hc : Nat.Coprime (2 ^ a) i :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hc.dvd_of_dvd_mul_left hd)
  rw [show k = a by omega]

theorem card_eq_of_isSylowTwoOf {S S' H : Subgroup G} (hS : QuasithinUnique.IsSylowTwoOf S H)
    (hS' : QuasithinUnique.IsSylowTwoOf S' H) : Nat.card S = Nat.card S' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  have h1 : S.relIndex H * Nat.card S = Nat.card H := by
    have := Subgroup.relIndex_mul_card (H := S) (K := H)
    rwa [inf_of_le_left hS.1] at this
  rw [hk, card_of_isSylowTwoOf hS' (a := k) (m := S.relIndex H) (by rw [← h1, hk, mul_comm])
    hS.2.2]

omit [Finite G] in
theorem card_sub (F : Frame125 T L V) (S : Finset (Fin 10))
    [DecidablePred fun x : Fin 10 → ZMod 2 => ∀ k ∉ S, x k = 0] :
    Nat.card ((F.sub S).subgroupOf V) =
      (Finset.univ.filter fun x : Fin 10 → ZMod 2 => ∀ k ∉ S, x k = 0).card :=
  S125L5a.card_of_coords F fun v => by
    rw [Subgroup.mem_subgroupOf, mem_sub_iff]

theorem card_V6_filter : (Finset.univ.filter fun x : Fin 10 → ZMod 2 =>
    ∀ k ∉ ({0, 1, 2, 4, 5, 7} : Finset (Fin 10)), x k = 0).card = 64 := by
  decide +kernel

theorem card_V1_filter : (Finset.univ.filter fun x : Fin 10 → ZMod 2 =>
    ∀ k ∉ ({0} : Finset (Fin 10)), x k = 0).card = 2 := by
  decide +kernel

omit [Finite G] in
theorem card_V1 (F : Frame125 T L V) : Nat.card F.V1 = 2 := by
  rw [← card_V1_filter, ← card_sub F {0}]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv.symm

omit [Finite G] in
theorem card_V6_sub (F : Frame125 T L V) : Nat.card (F.V6.subgroupOf V) = 64 := by
  rw [← card_V6_filter]
  exact card_sub F _

theorem card_R6 (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    Nat.card (autOn (ri T L F.V6) V) = 16 := by
  obtain ⟨-, -, -, -, -, f, hfs, hfk, -, -⟩ := (lemma12_5_2_of h1222 G T L V F hH).2.2.2
  have hf := S125Ex.Facts125.of h1222 hH
  have hker : f.ker = F.V6.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, hfk, Subgroup.mem_subgroupOf]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfs).toEquiv, hker,
    card_V6_sub, hf.card] at h1
  omega

theorem card_stab_w1' (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    Nat.card ↥(autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) F.w1') = 2 ^ 8 * 45 := by
  obtain ⟨hRC, hN, ⟨e⟩⟩ := S125L5c.part3 h1222 F hH
  set C := autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) F.w1'
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((autOn (ri T L F.V6) V).subgroupOf C)
  have h2 : Nat.card ((autOn (ri T L F.V6) V).subgroupOf C) = 16 := by
    rw [← card_R6 h1222 F hH]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv
  have h3 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  rw [Nat.card_congr e.toEquiv, h2, h3] at h1
  omega

omit [Finite G] in
theorem map_conj_eq {X : Type*} [Group X] {H : Subgroup X} {c : X} (hc : c ∈ H) :
    H.map (MulAut.conj c).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hc hy) (H.inv_mem hc)
  · intro hx
    refine ⟨c⁻¹ * x * c, H.mul_mem (H.mul_mem (H.inv_mem hc) hx) hc, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem card_stab (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) (w : ↥V)
    (hw : ∃ l ∈ L, l * (w : G) * l⁻¹ = F.v1') :
    Nat.card ↥(autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) w) = 2 ^ 8 * 45 := by
  obtain ⟨l, hlL, hlw⟩ := hw
  have hf := S125Ex.Facts125.of h1222 hH
  set c : MulAut ↥V := conjAct V ⟨l, hf.normalizes hlL⟩ with hcdef
  have hcL : c ∈ autOn L V := mem_autOn_iff_exists.mpr ⟨l, hf.normalizes hlL, hlL, rfl⟩
  have hcw : c • w = F.w1' := Subtype.ext hlw
  have h1 : autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) F.w1' =
      (autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) w).map (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, map_conj_eq hcL,
      ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hcw]
  rw [← card_stab_w1' h1222 F hH, h1,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem card_autOn_T (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    Nat.card (autOn T V) = 2 ^ 10 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have hS : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    SzN19.isSylowTwoOf_inf_of_normalizes
      (isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow le_sup_right) le_sup_left
      hH.hyp.normalizes le_rfl
  have h10 := S125ZV.card_autOn_sylow F hS hf.normalizes
  have hle : autOn (T ⊓ L) V ≤ autOn T V := A4.autOn_mono inf_le_left
  have hTL : autOn T V ≤ autOn L V := S125St.autOn_T_le F
  have hp : IsPGroup 2 (autOn T V) := CFSG.Quasithin.isPGroup_autOn hH.hyp.sylow.1 hf.T_le
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hkL : 2 ^ k ∣ 2 ^ 10 * 9765 := by
    rw [← hk, show (2 : ℕ) ^ 10 * 9765 = 9999360 by norm_num, ← card_sl_five_zmod_two,
      ← Nat.card_congr F.γ.toEquiv]
    exact Subgroup.card_dvd_of_le hTL
  have hc : Nat.Coprime (2 ^ k) 9765 := Nat.Coprime.pow_left k (by norm_num)
  have hk10 : k ≤ 10 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hc.dvd_of_dvd_mul_right hkL)
  have h10k : 2 ^ 10 ≤ 2 ^ k := by
    rw [← h10, ← hk]
    exact Subgroup.card_le_of_le hle
  have : 10 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).1 h10k
  rw [hk, show k = 10 by omega]

omit [Finite G] in
theorem eq_zpowers {P : Subgroup G} (hP : Nat.card P = 2) {w : G} (hwP : w ∈ P) (hw1 : w ≠ 1) :
    P = Subgroup.zpowers w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hw2 : w ^ 2 = 1 := by
    have h := pow_card_eq_one' (G := ↥P) (x := ⟨w, hwP⟩)
    rw [hP] at h
    exact congrArg Subtype.val h
  have ho : orderOf w = 2 := orderOf_eq_prime hw2 hw1
  symm
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le (G := G)).2 hwP) ?_
  rw [hP, Nat.card_zpowers, ho]

omit [Finite G] in
theorem mem_centralizer_iff_of_eq_zpowers {P : Subgroup G} {w : G} (hP : P = Subgroup.zpowers w)
    (x : G) : x ∈ Subgroup.centralizer (P : Set G) ↔ w * x = x * w := by
  constructor
  · intro hx
    exact Subgroup.mem_centralizer_iff.1 hx w (hP ▸ Subgroup.mem_zpowers w)
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hP] at hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((Commute.zpow_left hx k).eq)

theorem part1 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight) (h12210 : Stmt12_2_10)
    (F : Frame125 T L V) (hH : Hyp125 G T L V) (h7 : Concl12_5_7 T L V) :
    ∀ V₁' : Subgroup G, V₁' ≤ V → Nat.card V₁' = 2 →
      (¬ ∃ l ∈ L, CFSG.conjugate F.V1 l = V₁') →
      QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer (V₁' : Set G))
        (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V₁' : Set G)) →
        (T ⊓ Subgroup.centralizer (V₁' : Set G)).relIndex T = 4 ∧
        QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer (V₁' : Set G))
          (Subgroup.centralizer (V₁' : Set G)) ∧
        ∀ g : G, CFSG.conjugate F.V1 g ≠ V₁' := by
  intro P hPV hP2 hnot hSyl
  have hf := S125Ex.Facts125.of h1222 hH
  have hyp := hH.hyp
  have hV : IsElemAbelian 2 V := ⟨hf.comm, hf.sq⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hE : E6.HypE61 T M V :=
    S125L6a.hypE61_of_hyp h331 h1222 h323 h3228 hyp hV hyp.irrPlus.2.1 hf.le_T hf.T_le
      hf.normalizes
  have hP1 : P ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hP2; norm_num at hP2
  obtain ⟨w, hwP, hw1⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hP1
  have hPz := eq_zpowers hP2 hwP hw1
  have hCw := mem_centralizer_iff_of_eq_zpowers hPz
  set wV : ↥V := ⟨w, hPV hwP⟩ with hwV
  have hwl : ∃ l ∈ L, l * (wV : G) * l⁻¹ = F.v1' := by
    rcases S125L5b.part2 F w (hPV hwP) hw1 with ⟨l, hl, hlw⟩ | h
    · exfalso
      apply hnot
      refine ⟨l, hl, ?_⟩
      have hlw1 : l * w * l⁻¹ ≠ 1 := fun h => hw1 (by
        calc w = l⁻¹ * (l * w * l⁻¹) * l := by group
          _ = 1 := by rw [h]; group)
      have hV1 := eq_zpowers (card_V1 F) hlw hlw1
      rw [hPz, hV1]
      ext x
      change x ∈ (Subgroup.zpowers (l * w * l⁻¹)).map (MulAut.conj l⁻¹).toMonoidHom ↔ _
      rw [MonoidHom.map_zpowers]
      simp [mul_assoc]
    · exact h
  have hCMN : M ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    E6.inf_centralizer_le_normalizer hE hPV hP1
  have himg : autOn (M ⊓ Subgroup.centralizer (P : Set G)) V =
      autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) wV := by
    rw [← S125L6a.autOn_normalizer_eq h12210 hyp F]
    ext a
    constructor
    · intro ha
      obtain ⟨n, hnN, hn, rfl⟩ := mem_autOn_iff_exists.mp ha
      refine ⟨mem_autOn_iff_exists.mpr ⟨n, hnN, hn.1, rfl⟩, MulAction.mem_stabilizer_iff.2 ?_⟩
      apply Subtype.ext
      change n * w * n⁻¹ = w
      rw [← (hCw n).1 hn.2]
      group
    · rintro ⟨ha, hst⟩
      obtain ⟨n, hnN, hnM, rfl⟩ := mem_autOn_iff_exists.mp ha
      have hst' := MulAction.mem_stabilizer_iff.1 hst
      have h1 : n * w * n⁻¹ = w := congrArg Subtype.val hst'
      refine mem_autOn_iff_exists.mpr ⟨n, hnN, ⟨hnM, (hCw n).2 ?_⟩, rfl⟩
      calc w * n = n * w * n⁻¹ * n := by rw [h1]
        _ = n * w := by group
  have hcard_img : Nat.card (autOn (M ⊓ Subgroup.centralizer (P : Set G)) V) = 2 ^ 8 * 45 := by
    rw [himg]
    exact card_stab h1222 F hH wV hwl
  have hT1S := isSylowTwoOf_autOn' hSyl hCMN
  have hT1card : Nat.card (autOn (T ⊓ Subgroup.centralizer (P : Set G)) V) = 2 ^ 8 :=
    card_of_isSylowTwoOf hT1S hcard_img (by norm_num)
  have hT1N : T ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans hf.T_le
  have hCVP : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.centralizer_le hPV
  have hrel : (T ⊓ Subgroup.centralizer (P : Set G)).relIndex T = 4 := by
    have hA := card_autOn_eq_relIndex hT1N
    have hB := card_autOn_eq_relIndex hf.T_le
    rw [hT1card] at hA
    rw [card_autOn_T h1222 F hH] at hB
    have hinf : T ⊓ Subgroup.centralizer (P : Set G) ⊓ Subgroup.centralizer (V : Set G) =
        T ⊓ Subgroup.centralizer (V : Set G) := by
      rw [inf_assoc, inf_of_le_right hCVP]
    rw [hinf] at hA
    have hm := Subgroup.relIndex_mul_relIndex (T ⊓ Subgroup.centralizer (V : Set G))
      (T ⊓ Subgroup.centralizer (P : Set G)) T (inf_le_inf_left _ hCVP) inf_le_left
    rw [← hA, ← hB] at hm
    omega
  have hW : E3.wClos V 0 (T ⊓ Subgroup.centralizer (P : Set G)) = E3.wClos V 0 T := by
    apply le_antisymm
    · exact iSup₂_le fun A hA => le_iSup₂_of_le (f := fun A (_ : A ∈ E3.gammaSet V 0 T) => A) A
        ⟨hA.1.trans inf_le_left, hA.2⟩ le_rfl
    · refine iSup₂_le fun A hA => le_iSup₂_of_le
        (f := fun A (_ : A ∈ E3.gammaSet V 0 (T ⊓ Subgroup.centralizer (P : Set G))) => A) A
        ⟨le_inf hA.1 ?_, hA.2⟩ le_rfl
      exact ((le_iSup₂_of_le (f := fun A (_ : A ∈ E3.gammaSet V 0 T) => A) A hA le_rfl).trans
        h7.1).trans hCVP
  have hNT1 : Subgroup.normalizer ((T ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) ≤
      M := by
    have h1 := E3.normalizer_le_normalizer_wClos (V := V) (i := 0)
      (T ⊓ Subgroup.centralizer (P : Set G))
    rw [hW] at h1
    exact h1.trans h7.2.2
  have hSylC := E6.isSylowTwoOf_of_normalizer_le hSyl inf_le_right
    (inf_le_left.trans hyp.normalizes) hNT1
  refine ⟨hrel, hSylC, fun g hg => ?_⟩
  have hZV := frame125ZV_of h1222 G T L V F hH
  have hV1C : F.V1 ≤ Subgroup.centralizer (T : Set G) := by
    rw [← hZV]
    refine inf_le_right.trans ((Subgroup.closure_le _).2 ?_)
    rintro z ⟨⟨-, hz⟩, -⟩
    exact hz
  have hTC : T ≤ Subgroup.centralizer (F.V1 : Set G) := Subgroup.le_centralizer_iff.1 hV1C
  set Tg : Subgroup G := CFSG.conjugate T g with hTg
  have hTgC : Tg ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← hg] at hy
    have hx' : g * x * g⁻¹ ∈ T := mem_conjSubgroup_iff.1 hx
    have hy' : g * y * g⁻¹ ∈ F.V1 := mem_conjSubgroup_iff.1 hy
    have h1 := Subgroup.mem_centralizer_iff.1 (hTC hx') _ hy'
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h1]
      _ = x * y := by group
  have hTgS : QuasithinUnique.IsSylowTwoOf Tg (Subgroup.centralizer (P : Set G)) := by
    refine isSylowTwoOf_of_quasithinIsSylowTwo ⟨hyp.sylow.1.map _, ?_⟩ hTgC
    have hidx : Tg.index = T.index :=
      Subgroup.index_map_of_bijective (MulAut.conj g⁻¹).bijective T
    rw [hidx]
    exact hyp.sylow.2
  have hc1 := card_eq_of_isSylowTwoOf hSylC hTgS
  have hc2 : Nat.card Tg = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hc3 := Subgroup.relIndex_mul_card (H := T ⊓ Subgroup.centralizer (P : Set G)) (K := T)
  rw [inf_of_le_left inf_le_left, hrel, hc1, hc2] at hc3
  have hpos : 0 < Nat.card T := Nat.card_pos
  omega

end S125L9a

end CFSG.Quasithin.H13
