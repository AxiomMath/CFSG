module

public import CFSG.Quasithin.H13.A6S13816d
public import CFSG.Quasithin.H13.A6S13816e

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace L2Case

variable {G : Type} [Group G]

theorem three_dvd_card {X : Type} [Group X] (h : (∃ n, IsPSL 2 2 n X) ∨ IsAlt 5 X) :
    3 ∣ Nat.card X := by
  rcases h with ⟨n, hn⟩ | hA
  · obtain ⟨⟨-, hf, -⟩, K, hKf, hKfin, hK, ⟨e⟩⟩ := hn
    have h1 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 2)
      (by norm_num)
    have hodd : Nat.gcd 2 (2 ^ n - 1) = 1 := by
      have : Odd (2 ^ n - 1) := by
        have h2 : 2 ≤ 2 ^ n := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hf
        obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = 2 * k := ⟨2 ^ (n - 1), by
          rw [← pow_succ']
          congr 1
          omega⟩
        exact ⟨k - 1, by omega⟩
      exact Nat.coprime_two_left.mpr this
    have hcard : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, h1, hK, hodd]
      simp [Finset.Icc_self]
    have h4 : (2 ^ n) ^ 2 % 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, Nat.pow_mod]
      norm_num
    have hdvd : 3 ∣ (2 ^ n) ^ 2 - 1 := by
      have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega
    rw [hcard]
    exact hdvd.mul_left _
  · obtain ⟨e⟩ : Nonempty (X ≃* alternatingGroup (Fin 5)) := hA
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide

theorem isSolvable_comap {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hker : Group.IsSolvable f.ker) {Y : Subgroup B} (hY : Group.IsSolvable Y) :
    Group.IsSolvable (Y.comap f) := by
  let g : ↥(Y.comap f) →* ↥Y := (f.comp (Y.comap f).subtype).codRestrict Y fun x => x.2
  have hgk : Group.IsSolvable g.ker := by
    let i : ↥g.ker →* ↥f.ker :=
      { toFun := fun x => ⟨((x : ↥(Y.comap f)) : A), by
          have := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
          exact MonoidHom.mem_ker.mpr this⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hi : Function.Injective i := fun x y h => by
      have := congrArg (fun z : ↥f.ker => (z : A)) h
      exact Subtype.ext (Subtype.ext this)
    exact Group.isSolvable_of_isSolvable_injective hi
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])

theorem card_eq_ker_mul_range {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B) :
    Nat.card A = Nat.card f.ker * Nat.card f.range := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker

@[expose] def stabZ : Subgroup (Perm (Fin 6)) where
  carrier := {σ | act4f σ e0123 = e0123}
  one_mem' := act4f_one _ e0123_mem_W4
  mul_mem' := fun {a b} ha hb => by
    show act4f (a * b) e0123 = e0123
    rw [act4f_mul, show act4f b e0123 = e0123 from hb, show act4f a e0123 = e0123 from ha]
  inv_mem' := fun {a} ha => by
    show act4f a⁻¹ e0123 = e0123
    have h : act4f a e0123 = e0123 := ha
    conv_lhs => rw [← h]
    rw [← act4f_mul, inv_mul_cancel, act4f_one _ e0123_mem_W4]

instance : DecidablePred (· ∈ stabZ) := fun σ =>
  decidable_of_iff (act4f σ e0123 = e0123) Iff.rfl

theorem card_stabZ : Nat.card ↥stabZ = 48 := by
  have : Fintype.card {σ : Perm (Fin 6) // act4f σ e0123 = e0123} = 48 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

end L2Case

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem L1_le_conjClosure' (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h122 : CFSG.Quasithin.Lemma122A) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) (hne : conjClosure K T ≠ K)
    (h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) : S.L1 ≤ conjClosure K T := by
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hcard2 : Set.ncard (conjSubgroupsBy H K) = 2 := by
    rcases CFSG.Quasithin.lemma_1_2_1_three S.h13.qtke S.h13.simple S.h13.nonabelian h37 h38
      hH.1.2 hK with hn | ⟨h2, -⟩
    · exact absurd (L32Case.conjClosure_eq_of_normal hKH hTH hn) hne
    · exact h2
  have hcl := h122 G S.h13.simple S.h13.qtke S.h13.nonabelian H K hH.1.2 hK 3 Nat.prime_three
    (by norm_num) hcard2 h3
  have hN : H ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    normal_conjClosure_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian h37 h38
      hH.1.2 hTsyl hK
  refine (S.L1_le_closure_three hH).trans (hcl.le.trans (conjClosure_le fun h hh k hk => ?_))
  exact (Subgroup.mem_normalizer_iff.mp (hN hh) k).mp (le_conjClosure K T hk)

theorem inf_M_le_NV (h1334 : Stmt13_3_4) {H : Subgroup G} (hH : H ∈ S.Hz) :
    H ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  have hV : conjClosure (fsuV1 T V) L = V := (h1334 G T L V S.h13 S.irr).2.1
  rw [← hV]
  refine A5.le_normalizer_of_forall_conj_mem fun g hg v hv => ?_
  have hgz : g * S.z * g⁻¹ = S.z := by
    have h1 : g ∈ S.G1 := hH.2.1 hg.1
    rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
    rw [h1, mul_inv_cancel_right]
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, w, hw, rfl⟩ := hx
    have hlg : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg.2 l).mp hl
    have hwg : g * w * g⁻¹ ∈ fsuV1 T V := by
      rcases S.mem_V1_iff.1 hw with h | h
      · rw [h, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [h, hgz]
        exact S.mem_V1_iff.2 (Or.inr rfl)
    have e : g * (l * w * l⁻¹) * g⁻¹ = (g * l * g⁻¹) * (g * w * g⁻¹) * (g * l * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact mem_conjClosure hlg hwg
  | one => simp
  | mul x y _ _ ihx ihy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ih =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ih

theorem not_nine_dvd_card (h1337 : Stmt13_3_7) (hhat : ¬ IsHatA6 L) {H : Subgroup G}
    (hH : H ∈ S.Hz) {Y : Subgroup G} (hYH : Y ≤ H) (hYV : Y ≤ Subgroup.normalizer (V : Set G)) :
    ¬ 9 ∣ Nat.card Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3V : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G)) :=
    (h1337 G T L V S.h13 S.irr S.a6).resolve_right fun h => hhat h.1
  set N := Subgroup.normalizer (V : Set G) with hN
  set ψ := S.frame.ρ.comp (Y.subgroupOf N).subtype with hψ
  have hY' : Nat.card Y = Nat.card (Y.subgroupOf N) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYV).toEquiv).symm
  have hcard := L2Case.card_eq_ker_mul_range ψ
  have hker : ¬ 3 ∣ Nat.card ψ.ker := by
    intro h
    apply h3V
    refine h.trans (Subgroup.card_dvd_of_injective
      { toFun := fun x => ⟨(((x : ↥(Y.subgroupOf N)) : ↥N) : G), by
          have h1 : S.frame.ρ ((x : ↥(Y.subgroupOf N)) : ↥N) = 1 := MonoidHom.mem_ker.mp x.2
          exact (S.rho_eq_one_iff _).1 h1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl } fun x y h => ?_)
    have := congrArg (fun z : ↥(Subgroup.centralizer (V : Set G)) => (z : G)) h
    exact Subtype.ext (Subtype.ext (Subtype.ext this))
  have hrange : ψ.range ≤ L2Case.stabZ := by
    rintro _ ⟨y, rfl⟩
    have hyH : (((y : ↥(Y.subgroupOf N)) : ↥N) : G) ∈ H :=
      hYH (Subgroup.mem_subgroupOf.mp y.2)
    have hgz : (((y : ↥(Y.subgroupOf N)) : ↥N) : G) * S.z *
        (((y : ↥(Y.subgroupOf N)) : ↥N) : G)⁻¹ = S.z := by
      have h1 : (((y : ↥(Y.subgroupOf N)) : ↥N) : G) ∈ S.G1 := hH.2.1 hyH
      rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
      rw [h1, mul_inv_cancel_right]
    exact S.fix_e0123 _ hgz
  have h48 : Nat.card ψ.range ∣ 48 := L2Case.card_stabZ ▸ Subgroup.card_dvd_of_le hrange
  intro h9
  rw [hY', hcard] at h9
  have hcop : Nat.Coprime 9 (Nat.card ψ.ker) := by
    have : Nat.Coprime 3 (Nat.card ψ.ker) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hker
    simpa using Nat.Coprime.pow_left 2 this
  have h1 : 9 ∣ Nat.card ψ.range := hcop.dvd_of_dvd_mul_left h9
  have := h1.trans h48
  norm_num at this

theorem false_of_L2 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h122 : CFSG.Quasithin.Lemma122A) (h1334 : Stmt13_3_4) (h1337 : Stmt13_3_7)
    (h13 : Lem13813) (hS : S.Hyp138) (hhat : ¬ IsHatA6 L) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hne : conjClosure K T ≠ K)
    (hL2 : (∃ n, IsPSL 2 2 n (↥K ⧸ CFSG.pCore 2 ↥K)) ∨ IsAlt 5 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  set c : G := ((S.cL1 hhat : ↥(Subgroup.normalizer (V : Set G))) : G) with hcdef
  have hc : c ∈ S.L1 := S.cL1_mem hhat
  have hc3 : c ^ 3 = 1 := S.cL1_cube hhat
  have hcO : c ∉ pCoreOf 2 S.L1 := S.cL1_not_mem hhat
  have hdec : ∀ x ∈ S.L1, x ∈ pCoreOf 2 S.L1 ∨ c * c * x ∈ pCoreOf 2 S.L1 ∨
      c * x ∈ pCoreOf 2 S.L1 := fun x hx => S.L1_decomp hhat hx
  have hℓK : S.L1 ≤ conjClosure K T :=
    S.L1_le_conjClosure' h37 h38 h122 hH hK hne (L2Case.three_dvd_card hL2)
  have hℓH : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hO₂T : pCoreOf 2 S.L1 ≤ T := by
    have hTs : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow le_top
    have hsup : IsPGroup 2 ↥(T ⊔ pCoreOf 2 S.L1) :=
      hTs.2.1.to_sup_of_normal_right' (pCoreOf_isPGroup 2 S.L1)
        (S.T_le_normalizer_L1.trans (normalizer_le_normalizer_pCoreOf 2 S.L1))
    exact le_sup_right.trans (L2Comm.le_of_isSylowTwoOf hTs le_sup_left le_top hsup)
  have hN₀ : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Kb := (K.subgroupOf H).map π with hKb
  set Tb := (T.subgroupOf H).map π with hTb
  have hKbc : Kb ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := modO2Image_mem_cComp hK
  have hTbs : IsSylowTwoOf Tb ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hTsyl) π hπs
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH.1.2
  obtain ⟨-, hL2'⟩ := h38 _ hQ Kb hKbc
  rcases hL2' Tb hTbs with ⟨hnorm, -, -⟩ | ⟨t, htT, -, hconj, -, hcomm', hinf, hTN, -⟩
  · exact hne (L32Case.conjClosure_eq_of_normal hKH hTH (normal_of_normal_map_of_mem_cComp
      (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H) (subgroupOf_mem_cComp hK) hnorm))
  set K₂ := Kb.map (MulAut.conj t).toMonoidHom with hK₂
  set X := (S.L1.subgroupOf H).map π with hX
  have hXle : X ≤ Kb ⊔ K₂ := by
    have hcc : (conjClosure (K.subgroupOf H) (T.subgroupOf H)).map H.subtype =
        conjClosure K T := by
      rw [A3.map_conjClosure, Subgroup.map_subgroupOf_eq_of_le hKH,
        Subgroup.map_subgroupOf_eq_of_le hTH]
    have hcl : conjClosure (K.subgroupOf H) (T.subgroupOf H) ≤ (Kb ⊔ K₂).comap π := by
      refine conjClosure_le fun s hs k hk => ?_
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      have hs' : π s ∈ Tb := Subgroup.mem_map_of_mem π hs
      have hk' : π k ∈ Kb := Subgroup.mem_map_of_mem π hk
      have hmem : Kb.map (MulAut.conj (π s)).toMonoidHom ∈ conjSubgroupsBy Tb Kb :=
        ⟨π s, hs', rfl⟩
      rw [hconj] at hmem
      have hsk : π s * π k * (π s)⁻¹ ∈ Kb.map (MulAut.conj (π s)).toMonoidHom :=
        ⟨π k, hk', by simp [MulAut.conj_apply]⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · rw [h] at hsk
        exact Subgroup.mem_sup_left hsk
      · rw [h] at hsk
        exact Subgroup.mem_sup_right hsk
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ conjClosure K T := hℓK (Subgroup.mem_subgroupOf.mp hy)
    rw [← hcc] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    have hzy' : z = y := Subtype.ext hzy
    rw [← hzy']
    exact hcl hz
  have hTX : Tb ≤ Subgroup.normalizer (X : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    L32Case.map_le_normalizer_map S.T_le_normalizer_L1 π
  have hNp : IsPGroup 2 (((pCoreOf 2 S.L1).subgroupOf H).map π) := by
    have h1 : IsPGroup 2 ((pCoreOf 2 S.L1).subgroupOf H) :=
      (pCoreOf_isPGroup 2 S.L1).of_equiv
        (Subgroup.subgroupOfEquivOfLe ((pCoreOf_le 2 S.L1).trans hℓH)).symm
    exact h1.map π
  set cb := π ⟨c, hℓH hc⟩ with hcb
  have hcbX : cb ∈ X := ⟨⟨c, hℓH hc⟩, Subgroup.mem_subgroupOf.mpr hc, rfl⟩
  have hcH3 : (⟨c, hℓH hc⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simp [hc3])
  have hcb3 : cb ^ 3 = 1 := by rw [hcb, ← map_pow, hcH3, map_one]
  have hcb1 : cb ≠ 1 := by
    intro h
    have h' : ((⟨c, hℓH hc⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 := h
    have hmem := (QuotientGroup.eq_one_iff _).mp h'
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hmem⟩
    have hk' : c ^ 2 ^ k = 1 := by
      have := congrArg (fun w : ↥(CFSG.pCore 2 ↥H) => ((w : ↥H) : G)) hk
      simpa using this
    exact hcO (by rw [L32Comm.eq_one_of_pow_of_cube hk' hc3]; exact Subgroup.one_mem _)
  have hdecb : ∀ x ∈ X, x ∈ ((pCoreOf 2 S.L1).subgroupOf H).map π ∨
      cb * cb * x ∈ ((pCoreOf 2 S.L1).subgroupOf H).map π ∨
      cb * x ∈ ((pCoreOf 2 S.L1).subgroupOf H).map π := by
    rintro _ ⟨y, hy, rfl⟩
    rcases hdec y (Subgroup.mem_subgroupOf.mp hy) with h | h | h
    · exact Or.inl ⟨y, Subgroup.mem_subgroupOf.mpr h, rfl⟩
    · refine Or.inr (Or.inl ⟨⟨c, hℓH hc⟩ * ⟨c, hℓH hc⟩ * y, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩)
      · simpa using h
      · rw [hcb, map_mul, map_mul]
    · refine Or.inr (Or.inr ⟨⟨c, hℓH hc⟩ * y, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩)
      · simpa using h
      · rw [hcb, map_mul]
  obtain ⟨htwo, htwo', a, haK, b, hbK, hcab, ha3, ha1, hb3, hb1⟩ :=
    L2Comm.pair_split hcomm' hinf hXle (hTX htT)
      (L32Case.map_le_normalizer_map (le_normalizer_pCoreOf 2 S.L1) π) hNp hcbX hcb3 hcb1 hdecb
  have hcomm : ∀ x ∈ Kb, ∀ y ∈ K₂, x * y = y * x :=
    L32Comm.mul_comm_of_commutator_eq_bot hcomm'
  have hcomm2 : ∀ x ∈ K₂, ∀ y ∈ Kb, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hK₂c : K₂ ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := A38.cComp_conj hKbc
  have hU₁ : IsSylowTwoOf (Tb ⊓ Kb) Kb :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hKbc) hTbs
  have hU₂ : IsSylowTwoOf (Tb ⊓ K₂) K₂ :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK₂c) hTbs
  have haN := L2Comm.mem_normalizer_of_pair hcomm htwo hU₁ (inf_le_left.trans hTX) hcbX haK hbK
    hcab ha3
  have hcba : cb = b * a := by rw [hcab]; exact hcomm a haK b hbK
  have hbN := L2Comm.mem_normalizer_of_pair hcomm2 htwo' hU₂ (inf_le_left.trans hTX) hcbX hbK haK
    hcba hb3
  set B := (Kb ⊔ K₂) ⊓ Subgroup.normalizer ((Tb ⊓ Kb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
    Set (↥H ⧸ CFSG.pCore 2 ↥H)) ⊓ Subgroup.normalizer ((Tb ⊓ K₂ :
      Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) with hB
  have hBsol : Group.IsSolvable B := L2Comm.isSolvable_borel hcomm hinf hU₁ hU₂
  have haB : a ∈ B :=
    ⟨⟨Subgroup.mem_sup_left haK, haN⟩, L2Comm.mem_normalizer_of_comm hcomm2 hU₂.1 haK⟩
  have hbB : b ∈ B :=
    ⟨⟨Subgroup.mem_sup_right hbK, L2Comm.mem_normalizer_of_comm hcomm hU₁.1 hbK⟩, hbN⟩
  have hcbB : cb ∈ B := hcab ▸ B.mul_mem haB hbB
  have hK0N1 : Kb ⊔ K₂ ≤ Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    sup_le Subgroup.le_normalizer fun x hx => L2Comm.mem_normalizer_of_comm hcomm le_rfl hx
  have hK0N2 : Kb ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    sup_le (fun x hx => L2Comm.mem_normalizer_of_comm hcomm2 le_rfl hx) Subgroup.le_normalizer
  have hW : (Tb ⊓ Kb) ⊔ (Tb ⊓ K₂) = Tb ⊓ (Kb ⊔ K₂) := by
    apply le_antisymm
    · exact sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
    · intro u hu
      obtain ⟨k, hk⟩ := L32Comm.exists_pow_of_isPGroup hTbs.2.1 hu.1
      refine L2Comm.mem_sup_of_two_elt hcomm hinf hU₁ hU₂ hu.2 ?_ ?_ hk
      · exact F7.mem_normalizer_inf (Subgroup.le_normalizer hu.1) (hK0N1 hu.2)
      · exact F7.mem_normalizer_inf (Subgroup.le_normalizer hu.1) (hK0N2 hu.2)
  have hTB : Tb ≤ Subgroup.normalizer (B : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine A5.le_normalizer_of_forall_conj_mem fun s hs g hg => ?_
    have hgW : g ∈ Subgroup.normalizer ((Tb ⊓ (Kb ⊔ K₂) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      rw [← hW, ← A38.map_conj_eq_iff, Subgroup.map_sup, A38.map_conj_eq_iff.mpr hg.1.2,
        A38.map_conj_eq_iff.mpr hg.2]
    have hsW : s ∈ Subgroup.normalizer ((Tb ⊓ (Kb ⊔ K₂) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      F7.mem_normalizer_inf (Subgroup.le_normalizer hs) (hTN hs)
    have hsg : s * g * s⁻¹ ∈ Subgroup.normalizer ((Tb ⊓ (Kb ⊔ K₂) :
        Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hsW hgW) (Subgroup.inv_mem _ hsW)
    have hsgK : s * g * s⁻¹ ∈ Kb ⊔ K₂ := (Subgroup.mem_normalizer_iff.mp (hTN hs) g).mp hg.1.1
    refine ⟨⟨hsgK, ?_⟩, ?_⟩
    · have h1 := F7.mem_normalizer_inf hsg (hK0N1 hsgK)
      have e : Tb ⊓ (Kb ⊔ K₂) ⊓ Kb = Tb ⊓ Kb := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_left : Kb ≤ Kb ⊔ K₂)]
      rwa [e] at h1
    · have h1 := F7.mem_normalizer_inf hsg (hK0N2 hsgK)
      have e : Tb ⊓ (Kb ⊔ K₂) ⊓ K₂ = Tb ⊓ K₂ := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_right : K₂ ≤ Kb ⊔ K₂)]
      rwa [e] at h1
  have hYbsol : Group.IsSolvable ↥(B ⊔ Tb) :=
    C126.isSolvable_sup_of_le_normalizer' hTB hBsol (F1.isSolvable_of_isPGroup_two hTbs.2.1)
  set Y := ((B ⊔ Tb).comap π).map H.subtype with hY
  have hkerπ : Group.IsSolvable π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact isSolvable_pCore_two_group ↥H
  have hYsol : Group.IsSolvable Y := by
    have h1 := L2Case.isSolvable_comap π hkerπ hYbsol
    exact Group.isSolvable_of_surjective
      (f := (((B ⊔ Tb).comap π).equivMapOfInjective _ H.subtype_injective).toMonoidHom)
      (MulEquiv.surjective _)
  have hL1TY : S.L1 ⊔ T ≤ Y := by
    refine sup_le (fun x hx => ⟨⟨x, hℓH hx⟩, ?_, rfl⟩) (fun x hx => ⟨⟨x, hTH hx⟩, ?_, rfl⟩)
    · show π ⟨x, hℓH hx⟩ ∈ B ⊔ Tb
      rcases hdec x hx with h | h | h
      · exact Subgroup.mem_sup_right ⟨⟨x, hℓH hx⟩, Subgroup.mem_subgroupOf.mpr (hO₂T h), rfl⟩
      · have hm : c * c * x ∈ H := hℓH (S.L1.mul_mem (S.L1.mul_mem hc hc) hx)
        have e : (⟨x, hℓH hx⟩ : ↥H) =
            ((⟨c, hℓH hc⟩ : ↥H) * ⟨c, hℓH hc⟩)⁻¹ * ⟨c * c * x, hm⟩ := Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group)
        rw [e, map_mul, map_inv, map_mul]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
          (Subgroup.mem_sup_left hcbB) (Subgroup.mem_sup_left hcbB)))
          (Subgroup.mem_sup_right ⟨⟨c * c * x, hm⟩, Subgroup.mem_subgroupOf.mpr (hO₂T h), rfl⟩)
      · have hm : c * x ∈ H := hℓH (S.L1.mul_mem hc hx)
        have e : (⟨x, hℓH hx⟩ : ↥H) = (⟨c, hℓH hc⟩ : ↥H)⁻¹ * ⟨c * x, hm⟩ := Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group)
        rw [e, map_mul, map_inv]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hcbB))
          (Subgroup.mem_sup_right ⟨⟨c * x, hm⟩, Subgroup.mem_subgroupOf.mpr (hO₂T h), rfl⟩)
    · show π ⟨x, hTH hx⟩ ∈ B ⊔ Tb
      exact Subgroup.mem_sup_right ⟨⟨x, hTH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hYG1 : Y ≤ S.G1 := (Subgroup.map_subtype_le _).trans hH.2.1
  have hYM : Y ≤ Subgroup.normalizer (L : Set G) := h13 G T L V S hS Y hL1TY hYG1 hYsol
  set B₀ := (B.comap π).map H.subtype with hB₀
  have hB₀H : B₀ ≤ H := Subgroup.map_subtype_le _
  have hB₀Y : B₀ ≤ Y := Subgroup.map_mono (Subgroup.comap_mono le_sup_left)
  have hB₀V : B₀ ≤ Subgroup.normalizer (V : Set G) :=
    (le_inf hB₀H (hB₀Y.trans hYM)).trans (S.inf_M_le_NV h1334 hH)
  have h9 : 9 ∣ Nat.card B₀ := by
    have h1 := L2Comm.nine_dvd_card (B := B) hinf (fun g (hg : g ∈ B) => hK0N1 hg.1.1) haB haK
      ha3 ha1 hbB hbK hb3 hb1
    have h2 : Nat.card B ∣ Nat.card (B.comap π) := by
      have := Subgroup.card_map_dvd (B.comap π) π
      rwa [Subgroup.map_comap_eq_self_of_surjective hπs] at this
    have h3 : Nat.card B₀ = Nat.card (B.comap π) :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [h3]
    exact h1.trans h2
  exact S.not_nine_dvd_card h1337 hhat hH hB₀H hB₀V h9

end Setting4

@[expose] def Case13816L2Hat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    IsHatA6 L → ∀ H ∈ S.Hz, ∀ K ∈ cComp H, conjClosure K T ≠ K → H = (K ⊔ T) ⊔ S.L1 →
      ¬ ((∃ n, IsPSL 2 2 n (↥K ⧸ CFSG.pCore 2 ↥K)) ∨ IsAlt 5 (↥K ⧸ CFSG.pCore 2 ↥K))

theorem case13816L2_of (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h122 : CFSG.Quasithin.Lemma122A) (h1334 : Stmt13_3_4) (h1337 : Stmt13_3_7)
    (h13 : Lem13813) (hHat : Case13816L2Hat) : Case13816L2 := by
  intro G _ _ T L V S hS H hH K hK hne hHeq hL2
  by_cases hhat : IsHatA6 L
  · exact hHat G T L V S hS hhat H hH K hK hne hHeq hL2
  · exact S.false_of_L2 h37 h38 h122 h1334 h1337 h13 hS hhat hH hK hne hL2

end CFSG.Quasithin.H13.A6

