module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaNbrGrpAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaNbrGrpAux2
public import CFSG.Quasithin.Background.A318PC7

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem E6QTwo.three_pow_six_dvd_card_center_quot {Bs K' : Subgroup G} {y : G}
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs) (hyB : y ∈ Bs)
    (hK'y : K' ≤ Subgroup.centralizer {y}) (hBsN : Bs ≤ Subgroup.normalizer (K' : Set G))
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K' Bs, φ b = b) → b ∈ Subgroup.zpowers ⟨y, hyB⟩)
    (h9 : 9 ∣ Nat.card (ggAutomizer K' Bs))
    (hC : Nat.card (Subgroup.closure
      {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}) = 3 ^ 4)
    (hyC : (⟨y, hyB⟩ : ↥Bs) ∉
      Subgroup.closure {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}) :
    3 ^ 6 ∣ Nat.card (K' ⧸ Subgroup.center K') := by
  classical
  let Cb : Subgroup ↥Bs :=
    Subgroup.closure {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}
  let Cg : Subgroup G := Cb.map Bs.subtype
  let Zc : Subgroup G := (Subgroup.center ↥K').map K'.subtype
  let N : Subgroup G := K' ⊓ Subgroup.normalizer (Bs : Set G)
  let M : Subgroup G := N ⊓ Subgroup.centralizer (Bs : Set G)
  let A : Subgroup (MulAut ↥Bs) := ggAutomizer K' Bs
  have hCb : Nat.card Cb = 3 ^ 4 := hC
  have hyC' : (⟨y, hyB⟩ : ↥Bs) ∉ Cb := hyC
  have hy1 : y ≠ 1 := E6QTwo.y_ne_one_of_notMem_closure hyB hyC'
  have hCgK : Cg ≤ K' := E6QTwo.closure_map_subtype_le_of_le_normalizer hBsN
  have hCgcard : Nat.card Cg = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective Bs.subtype_injective, hCb]
  have hCgBs : Cg ≤ Bs := Subgroup.map_subtype_le _
  have hCgN : Cg ≤ N := by
    refine le_inf hCgK ?_
    exact hCgBs.trans (Subgroup.le_normalizer)
  have hCgCent : Cg ≤ Subgroup.centralizer (Bs : Set G) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    simpa using congrArg Subtype.val (isMulCommutative_iff.mp hBs.1 ⟨c, hc⟩ b)
  have hCgM : Cg ≤ M := le_inf hCgN hCgCent
  have hNZM : N ⊓ Zc ≤ M := by
    rintro z ⟨hzN, hzZ⟩
    exact ⟨hzN, E6QTwo.centralizes_of_mem_center_inf_normalizer hBs hNT hyB hy1 hK'y hBsN
      hfix hzN.2 hzZ⟩
  have hCZ : Cg ⊓ Zc = ⊥ := by
    have h := E6QTwo.closure_map_subtype_inf_center_eq_bot hBs hyB hfix hyC'
    simpa [Cg, Zc, Cb] using h
  have hMZ : M ⊓ Zc = N ⊓ Zc := by
    refine le_antisymm (inf_le_inf_right Zc inf_le_left) ?_
    rintro z ⟨hzN, hzZ⟩
    exact ⟨hNZM ⟨hzN, hzZ⟩, hzZ⟩
  have hMN : M ≤ N := inf_le_left
  have hMK : M ≤ K' := hMN.trans inf_le_left
  have hNK : N ≤ K' := inf_le_left
  have hNB : N ≤ Subgroup.normalizer (Bs : Set G) := inf_le_right
  let πK : ↥K' →* (↥K' ⧸ Subgroup.center ↥K') := QuotientGroup.mk' (Subgroup.center ↥K')
  let fM : ↥M →* (↥K' ⧸ Subgroup.center ↥K') := πK.comp (Subgroup.inclusion hMK)
  have hdvdC : 3 ^ 4 ∣ Nat.card fM.range := by
    let fC : ↥Cg →* (↥K' ⧸ Subgroup.center ↥K') := πK.comp (Subgroup.inclusion (hCgK))
    have hinj : Function.Injective fC := by
      rw [← MonoidHom.ker_eq_bot_iff]
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_bot]
      constructor
      · intro hx
        apply Subtype.ext
        have hx' : (Subgroup.inclusion hCgK x : ↥K') ∈ Subgroup.center ↥K' :=
          (QuotientGroup.eq_one_iff _).mp hx
        have hxCZ : (x : G) ∈ Cg ⊓ Zc :=
          ⟨x.2, Subgroup.mem_map.mpr ⟨Subgroup.inclusion hCgK x, hx', rfl⟩⟩
        rw [hCZ] at hxCZ
        exact Subgroup.mem_bot.mp hxCZ
      · intro hx
        rw [hx]
        simp
    have hcard : Nat.card fC.range = 3 ^ 4 := by
      have h1 : Nat.card fC.range = Nat.card ↥Cg := by
        change Nat.card ↥(Set.range fC) = Nat.card ↥Cg
        exact (Nat.card_congr (Equiv.ofInjective fC hinj)).symm
      rw [h1, hCgcard]
    have hle : fC.range ≤ fM.range := by
      rintro x ⟨c, rfl⟩
      refine ⟨⟨(c : G), hCgM c.2⟩, ?_⟩
      change πK ⟨(c : G), hMK (hCgM c.2)⟩ = πK ⟨(c : G), hCgK c.2⟩
      rw [show (⟨(c : G), hMK (hCgM c.2)⟩ : ↥K') = ⟨(c : G), hCgK c.2⟩ from
        Subtype.ext rfl]
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hle
  let ψhom : ↥N →* MulAut ↥Bs :=
    (Subgroup.normalizerMonoidHom (H := Bs)).comp (Subgroup.inclusion hNB)
  let φ : ↥N →* ↥A :=
    { toFun := fun g => ⟨ψhom g, by
        have hψ : ψhom g = ggConjAut Bs (hNB g.2) := by
          ext b
          exact Subgroup.normalizerMonoidHom_apply_apply_coe (H := Bs) ⟨g, hNB g.2⟩ b
        rw [hψ]
        exact ggConjAut_mem_ggAutomizer g.2.1 (hNB g.2)⟩
      map_one' := Subtype.ext (map_one ψhom)
      map_mul' := fun g h => Subtype.ext (map_mul ψhom g h) }
  have hφsurj : Function.Surjective φ := by
    intro a
    obtain ⟨g, hgK, hgN, hg⟩ := mem_ggAutomizer_iff.mp a.2
    refine ⟨⟨g, ⟨hgK, hgN⟩⟩, ?_⟩
    apply Subtype.ext
    have hψ : ψhom ⟨g, ⟨hgK, hgN⟩⟩ = ggConjAut Bs hgN := by
      ext b
      exact Subgroup.normalizerMonoidHom_apply_apply_coe (H := Bs) ⟨g, hgN⟩ b
    change ψhom ⟨g, ⟨hgK, hgN⟩⟩ = a.1
    rw [hψ]
    ext b
    rw [ggConjAut_apply]
    exact (hg b).symm
  have hker : Nat.card φ.ker = Nat.card ↥M := by
    have hkerEq : φ.ker = M.subgroupOf N := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      have hψ : ψhom g = ggConjAut Bs (hNB g.2) := by
        ext b
        exact Subgroup.normalizerMonoidHom_apply_apply_coe (H := Bs) ⟨g, hNB g.2⟩ b
      constructor
      · intro hg
        have hg' : ggConjAut Bs (hNB g.2) = 1 := by
          rw [← hψ]
          exact congrArg Subtype.val hg
        refine ⟨g.2, ?_⟩
        change (g : G) ∈ Subgroup.centralizer (Bs : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have h1 := congrArg (fun f : MulAut ↥Bs => ((f ⟨b, hb⟩ : ↥Bs) : G)) hg'
        simp only [MulAut.one_apply, ggConjAut_apply] at h1
        have hgb : (g : G) * (b : G) = (b : G) * (g : G) := by
          calc (g : G) * (b : G) = (g : G) * (b : G) * (g : G)⁻¹ * (g : G) := by group
            _ = (b : G) * (g : G) := by rw [h1]
        exact hgb.symm
      · rintro ⟨-, hgcent⟩
        apply Subtype.ext
        change ψhom g = 1
        rw [hψ]
        ext b
        rw [ggConjAut_apply, MulAut.one_apply]
        have hcomm := Subgroup.mem_centralizer_iff.mp hgcent b b.2
        rw [hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hkerEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMN).toEquiv
  have hNA : Nat.card ↥N = Nat.card ↥A * Nat.card ↥M := by
    have h := Subgroup.card_ker_mul_card_of_surjective hφsurj
    rw [hker] at h
    rw [mul_comm] at h
    exact h.symm
  let fN : ↥N →* (↥K' ⧸ Subgroup.center ↥K') := πK.comp (Subgroup.inclusion hNK)
  have hkerN : Nat.card fN.ker = Nat.card ↥(N ⊓ Zc) := by
    have hkerEq : fN.ker = (N ⊓ Zc).subgroupOf N := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro hg
        refine ⟨g.2, ?_⟩
        have hg' : (Subgroup.inclusion hNK g : ↥K') ∈ Subgroup.center ↥K' :=
          (QuotientGroup.eq_one_iff _).mp hg
        exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hNK g, hg', rfl⟩
      · rintro ⟨-, hgZ⟩
        obtain ⟨zK, hzKc, hzKval⟩ := Subgroup.mem_map.mp hgZ
        change (QuotientGroup.mk (Subgroup.inclusion hNK g) : ↥K' ⧸ Subgroup.center ↥K') = 1
        rw [QuotientGroup.eq_one_iff]
        have hEq : (Subgroup.inclusion hNK g : ↥K') = zK := by
          apply Subtype.ext
          change ((Subgroup.inclusion hNK g : ↥K') : G) = K'.subtype zK
          rw [hzKval]
          rfl
        rw [hEq]
        exact hzKc
    rw [hkerEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hkerM : Nat.card fM.ker = Nat.card ↥(M ⊓ Zc) := by
    have hkerEq : fM.ker = (M ⊓ Zc).subgroupOf M := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro hg
        refine ⟨g.2, ?_⟩
        have hg' : (Subgroup.inclusion hMK g : ↥K') ∈ Subgroup.center ↥K' :=
          (QuotientGroup.eq_one_iff _).mp hg
        exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hMK g, hg', rfl⟩
      · rintro ⟨-, hgZ⟩
        obtain ⟨zK, hzKc, hzKval⟩ := Subgroup.mem_map.mp hgZ
        change (QuotientGroup.mk (Subgroup.inclusion hMK g) : ↥K' ⧸ Subgroup.center ↥K') = 1
        rw [QuotientGroup.eq_one_iff]
        have hEq : (Subgroup.inclusion hMK g : ↥K') = zK := by
          apply Subtype.ext
          change ((Subgroup.inclusion hMK g : ↥K') : G) = K'.subtype zK
          rw [hzKval]
          rfl
        rw [hEq]
        exact hzKc
    rw [hkerEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hNbar : Nat.card fN.range = Nat.card ↥A * Nat.card fM.range := by
    have hN := Subgroup.card_ker_mul_card_range fN
    rw [hkerN] at hN
    have hM := Subgroup.card_ker_mul_card_range fM
    rw [hkerM] at hM
    have hN' : Nat.card fN.range * Nat.card ↥(N ⊓ Zc) = Nat.card ↥N := by
      rw [mul_comm]
      exact hN
    have hM' : Nat.card fM.range * Nat.card ↥(M ⊓ Zc) = Nat.card ↥M := by
      rw [mul_comm]
      exact hM
    have hMZcard : Nat.card ↥(M ⊓ Zc) = Nat.card ↥(N ⊓ Zc) := by rw [hMZ]
    have h1 : Nat.card fN.range * Nat.card ↥(N ⊓ Zc) =
        Nat.card ↥A * Nat.card fM.range * Nat.card ↥(N ⊓ Zc) := by
      calc Nat.card fN.range * Nat.card ↥(N ⊓ Zc)
          = Nat.card ↥N := hN'
        _ = Nat.card ↥A * Nat.card ↥M := hNA
        _ = Nat.card ↥A * (Nat.card fM.range * Nat.card ↥(M ⊓ Zc)) := by rw [hM']
        _ = Nat.card ↥A * Nat.card fM.range * Nat.card ↥(N ⊓ Zc) := by
            rw [hMZcard]; ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) h1
  have hdvdNbar : 3 ^ 6 ∣ Nat.card fN.range := by
    rw [hNbar]
    have h : 9 * 3 ^ 4 ∣ Nat.card ↥A * Nat.card fM.range := mul_dvd_mul h9 hdvdC
    rwa [show (9 * 3 ^ 4 : ℕ) = 3 ^ 6 by norm_num] at h
  exact hdvdNbar.trans (Subgroup.card_subgroup_dvd_card fN.range)

theorem E6QTwo.isCyclic_of_le_centralizer_of_nbr {Bs K' : Subgroup G} {y : G}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5) (hyB : y ∈ Bs)
    (hK'y : K' ≤ Subgroup.centralizer {y}) (hBsN : Bs ≤ Subgroup.normalizer (K' : Set G))
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K' Bs, φ b = b) → b ∈ Subgroup.zpowers ⟨y, hyB⟩)
    (hC : Nat.card (Subgroup.closure
      {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}) = 3 ^ 4)
    (hyC : (⟨y, hyB⟩ : ↥Bs) ∉
      Subgroup.closure {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}) :
    ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (K' : Set G) → IsCyclic S := by
  classical
  let Cb : Subgroup ↥Bs :=
    Subgroup.closure {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}
  let Cg : Subgroup G := Cb.map Bs.subtype
  have hCb : Nat.card Cb = 3 ^ 4 := hC
  have hyC' : (⟨y, hyB⟩ : ↥Bs) ∉ Cb := hyC
  have hy1 : y ≠ 1 := E6QTwo.y_ne_one_of_notMem_closure hyB hyC'
  let Ck : Subgroup G := Subgroup.centralizer (K' : Set G)
  have hyCk : y ∈ Ck := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hK'y hk)
  let H := ↥Ck
  let yH : H := ⟨y, hyCk⟩
  have hyH1 : yH ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hyH3 : yH ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hBs.2 y hyB
  have hyHord : orderOf yH = 3 := orderOf_eq_prime hyH3 hyH1
  let Z : Subgroup H := Subgroup.zpowers yH
  have hZcard : Nat.card Z = 3 := by
    rw [Nat.card_zpowers, hyHord]
  have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hZcard, pow_one])
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hyP⟩ := hZp.exists_le_sylow
  have hyP' : yH ∈ (P : Subgroup H) := hyP (Subgroup.mem_zpowers yH)
  let Q : Subgroup H := (P : Subgroup H) ⊓ Subgroup.centralizer ({yH} : Set H)
  have hQP : Q ≤ (P : Subgroup H) := inf_le_left
  have hQy : Q ≤ Subgroup.centralizer ({yH} : Set H) := inf_le_right
  have hyQ : yH ∈ Q :=
    ⟨hyP', Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let Q' : Subgroup G := Q.map Ck.subtype
  have hQ'y : Q' ≤ Subgroup.centralizer ({y} : Set G) := by
    intro g hg
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hg
    have h := congrArg (fun x : H => (x : G))
      (Subgroup.mem_centralizer_singleton_iff.mp (hQy hq))
    exact Subgroup.mem_centralizer_singleton_iff.mpr h
  have hQ'K : Q' ≤ Subgroup.centralizer (K' : Set G) := by
    intro g hg
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hg
    exact q.2
  have hQ'Bs : Q' ≤ Subgroup.centralizer (Bs : Set G) :=
    E6QTwo.isPGroup_le_centralizer_bstar hBs hcard hyB hBsN hCb hyC' hQ'y hQ'K
  have hQp : IsPGroup 3 Q :=
    (P.2).of_injective (Subgroup.inclusion hQP) (Subgroup.inclusion_injective hQP)
  have hQcyc : IsCyclic Q := by
    refine CFSG.Quasithin.A318P.isCyclic_of_unique_three (R := Q) (Z := Z) hQp hZcard ?_
    intro r hrQ hrord
    have hr3 : r ^ 3 = 1 := by rw [← hrord]; exact pow_orderOf_eq_one r
    have hrCk : (r : G) ∈ Ck := r.2
    have hrQ' : (r : G) ∈ Q' := Subgroup.mem_map_of_mem Ck.subtype hrQ
    have hrCent : (r : G) ∈ Subgroup.centralizer (Bs : Set G) := hQ'Bs hrQ'
    have hrGord : orderOf (r : G) = 3 := by
      rw [Subgroup.orderOf_coe r]
      exact hrord
    have hrG3 : (r : G) ^ 3 = 1 := by
      rw [← hrGord]
      exact pow_orderOf_eq_one (r : G)
    have hrBs : (r : G) ∈ Bs := hstar (r : G) hrCent hrG3
    let rB : ↥Bs := ⟨(r : G), hrBs⟩
    have hrBfix : ∀ φ ∈ ggAutomizer K' Bs, φ rB = rB := by
      intro φ hφ
      obtain ⟨g, hgK, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
      apply Subtype.ext
      rw [hg rB]
      have hcomm : g * (r : G) = (r : G) * g :=
        Subgroup.mem_centralizer_iff.mp hrCk g hgK
      rw [hcomm, mul_inv_cancel_right]
    have hrz : rB ∈ Subgroup.zpowers ⟨y, hyB⟩ := hfix rB hrBfix
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hrz
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    apply Subtype.ext
    have hk' := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at hk'
    exact hk'
  have hQeqP : Q = (P : Subgroup H) := by
    refine le_antisymm hQP ?_
    by_contra hnot
    have hlt : Q.subgroupOf (P : Subgroup H) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hnot
      have hcardEq : Nat.card Q = Nat.card (P : Subgroup H) := by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, htop,
          Subgroup.card_top]
      exact (Subgroup.eq_of_le_of_card_ge hQP hcardEq.ge).ge
    haveI : Group.IsNilpotent ↥(P : Subgroup H) := (P.2).isNilpotent
    have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥(P : Subgroup H))
      (Q.subgroupOf (P : Subgroup H)) hlt
    obtain ⟨n', hn'N, hn'Q⟩ := IsConcreteLE.exists_of_lt hnc
    let nH : H := (n' : H)
    have hnH_P : nH ∈ (P : Subgroup H) := n'.2
    have hnNQ : nH ∈ Subgroup.normalizer (Q : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro q
      constructor
      · intro hq
        have hqP : q ∈ (P : Subgroup H) := hQP hq
        have h := (Subgroup.mem_normalizer_iff.mp hn'N (⟨q, hqP⟩ : ↥(P : Subgroup H))).mp
          (Subgroup.mem_subgroupOf.mpr hq)
        exact Subgroup.mem_subgroupOf.mp h
      · intro hq
        have hqP : q ∈ (P : Subgroup H) := by
          have hqP' : nH * q * nH⁻¹ ∈ (P : Subgroup H) := hQP hq
          have hinv : nH⁻¹ ∈ (P : Subgroup H) := (P : Subgroup H).inv_mem hnH_P
          have hm : nH⁻¹ * (nH * q * nH⁻¹) * nH ∈ (P : Subgroup H) :=
            (P : Subgroup H).mul_mem ((P : Subgroup H).mul_mem hinv hqP') hnH_P
          have heq : nH⁻¹ * (nH * q * nH⁻¹) * nH = q := by
            calc nH⁻¹ * (nH * q * nH⁻¹) * nH
                = (nH⁻¹ * nH) * q * (nH⁻¹ * nH) := by group
              _ = q := by rw [inv_mul_cancel]; simp
          rwa [heq] at hm
        have hq' : nH * q * nH⁻¹ ∈ Q := hq
        have hmem : (⟨q, hqP⟩ : ↥(P : Subgroup H)) ∈ Q.subgroupOf (P : Subgroup H) :=
          (Subgroup.mem_normalizer_iff.mp hn'N (⟨q, hqP⟩ : ↥(P : Subgroup H))).mpr
            (Subgroup.mem_subgroupOf.mpr hq')
        exact Subgroup.mem_subgroupOf.mp hmem
    have hZP : Subgroup.zpowers nH ≤ (P : Subgroup H) := Subgroup.zpowers_le.mpr hnH_P
    have hnP : IsPGroup 3 (Subgroup.zpowers nH) :=
      (P.2).of_injective (Subgroup.inclusion hZP) (Subgroup.inclusion_injective hZP)
    have hncent : nH * yH * nH⁻¹ = yH :=
      E6QTwo.eq_of_isPGroup_normalizes_isCyclic_three hQcyc hyQ hyH1 hyH3 hnNQ hnP
    have hcomm : nH * yH = yH * nH := by
      calc nH * yH = (nH * yH * nH⁻¹) * nH := by
            rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = yH * nH := by rw [hncent]
    have hnQ : nH ∈ Q :=
      ⟨hnH_P, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    exact hn'Q (Subgroup.mem_subgroupOf.mpr hnQ)
  have hPcyc : IsCyclic (P : Subgroup H) := hQeqP ▸ hQcyc
  intro S hS hSK
  have hS' : IsPGroup 3 (S.subgroupOf Ck) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  obtain ⟨P', hP'⟩ := hS'.exists_le_sylow
  have hP'cyc : IsCyclic (P' : Subgroup H) :=
    (Sylow.equiv P P').isCyclic.mp hPcyc
  haveI : IsCyclic (P' : Subgroup H) := hP'cyc
  have hS'cyc : IsCyclic (S.subgroupOf Ck) := Subgroup.isCyclic_of_le hP'
  exact (Subgroup.subgroupOfEquivOfLe hSK).isCyclic.mp hS'cyc

end CFSG.StandardType

end
