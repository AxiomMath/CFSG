module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivStabAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
public import CFSG.LocalAnalysis.StandardType.GGP3LineNormalizer

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwoLMDivStab_ggInduced_inv {G : Type} [Group G] {Bs : Subgroup G}
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) : φ⁻¹ ∈ ggInduced ⊤ Bs := by
  simp only [ggInduced] at hφ ⊢
  obtain ⟨g, -, hgN, hgφ⟩ := hφ
  refine ⟨g⁻¹, Subgroup.mem_top g⁻¹, Subgroup.inv_mem _ hgN, fun b => ?_⟩
  have h1 := hgφ (φ⁻¹ b)
  have h2 : φ (φ⁻¹ b) = b := by simp
  rw [h2] at h1
  rw [h1]
  group

theorem qTwoLMDivStab_ggInduced_mul {G : Type} [Group G] {Bs : Subgroup G}
    {φ ψ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) (hψ : ψ ∈ ggInduced ⊤ Bs) :
    φ * ψ ∈ ggInduced ⊤ Bs := by
  simp only [ggInduced] at hφ hψ ⊢
  obtain ⟨g, -, hgN, hgφ⟩ := hφ
  obtain ⟨h, -, hhN, hhψ⟩ := hψ
  refine ⟨g * h, Subgroup.mem_top _, Subgroup.mul_mem _ hgN hhN, fun b => ?_⟩
  rw [MulAut.mul_apply, hgφ, hhψ]
  group

theorem qTwoLMDivStab_card_Qm (m : ℕ) (hm : 1 ≤ m) : Nat.card (QTwoQm m) = 3 ^ (m - 1) := by
  let K : Subgroup (Fin m → Multiplicative (ZMod 3)) :=
    Subgroup.zpowers (fun _ => Multiplicative.ofAdd (1 : ZMod 3))
  have hKcard : Nat.card ↥K = 3 := by
    rw [Nat.card_zpowers]
    have horder : orderOf (fun _ => Multiplicative.ofAdd (1 : ZMod 3) :
        Fin m → Multiplicative (ZMod 3)) = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      rw [orderOf_eq_prime (p := 3)]
      · ext i
        rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_nsmul, nsmul_eq_mul]
        exact ZMod.natCast_self 3
      · intro h
        have := congrFun h ⟨0, by omega⟩
        simp at this
    exact horder
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  rw [hKcard] at hcard
  rw [show Nat.card (Fin m → Multiplicative (ZMod 3)) = 3 ^ m by simp] at hcard
  have hmul : 3 ^ m = 3 ^ (m - 1) * 3 := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < (3 : ℕ)) (hcard.symm.trans hmul)

theorem qTwoLMDivStab_card_W {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    {m : ℕ} {VT : Type} [Group VT] (F : QTwoFrame m (QTwoQm m) VT Bs L x)
    (hm : 1 ≤ m) (hV : IsQmModel m (QTwoQm m) F.permV) :
    Nat.card ↥(ggGamma L F.hN).range = 3 ^ (m - 1) := by
  rw [← Nat.card_congr F.theta.toEquiv]
  exact qTwoLMDivStab_card_Qm m hm

theorem qTwoLMDivStab_card_Bs {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    {m : ℕ} {VT : Type} [Group VT] (F : QTwoFrame m (QTwoQm m) VT Bs L x)
    (hm : 1 ≤ m) (hV : IsQmModel m (QTwoQm m) F.permV) : Nat.card ↥Bs = 3 ^ m := by
  have hker : (ggGamma L F.hN).ker = (Subgroup.zpowers x).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, F.ker b, Subgroup.mem_subgroupOf]
  have hcard_ker : Nat.card ↥(ggGamma L F.hN).ker = 3 := by
    rw [hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr F.hx)).toEquiv,
      Nat.card_zpowers, F.hord]
  have hcard := Subgroup.card_ker_mul_card_range (ggGamma L F.hN)
  rw [hcard_ker, qTwoLMDivStab_card_W F hm hV] at hcard
  rw [← hcard, mul_comm 3 (3 ^ (m - 1)), ← pow_succ, Nat.sub_add_cancel hm]

theorem qTwoLMDivStab_shear {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m : ℕ}
    (F : QTwoFrame m (QTwoQm m) ↥(sumZero m 3) Bs L x) (hG : GGThmIHyp 3 B x L)
    (hrt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hm : 6 ≤ m)
    (hV : IsQmModel m (QTwoQm m) F.permV) (hVT : IsAugModel m ↥(sumZero m 3) F.permVT)
    (hrigid : ∀ U : Subgroup (QTwoQm m), (∀ (σ : Equiv.Perm (Fin m)) (u : QTwoQm m), u ∈ U →
      F.permV σ u ∈ U) → Nat.card (QTwoQm m) ≤ 3 * Nat.card U →
      ∀ ψ : MulAut (QTwoQm m),
      (∀ σ, ∃ σ', ψ * F.permV σ * ψ⁻¹ = F.permV σ') → (∀ u ∈ U, ψ u = u) → ψ = 1)
    {δ : MulAut ↥Bs} (hδ : δ ∈ ggInduced ⊤ Bs)
    (hδx : δ ⟨x, F.hx⟩ = ⟨x, F.hx⟩) (hδT : ∀ b : ↥Bs, (b : G) ∈ L → δ b = b) : δ = 1 := by
  classical
  have hδI : δ ∈ ggInduced ⊤ Bs := hδ
  simp only [ggInduced] at hδ
  obtain ⟨g, -, hgBs, hgδ⟩ := hδ
  have hδeq : δ = ggConjAut Bs hgBs := by
    ext b
    rw [ggConjAut_apply]
    exact hgδ b
  have hgx_eq : g * x * g⁻¹ = x := by
    have h := hgδ ⟨x, F.hx⟩
    have hxval : ((δ ⟨x, F.hx⟩ : ↥Bs) : G) = x := by
      simpa using congrArg Subtype.val hδx
    rw [hxval] at h
    simpa using h.symm
  have hgx : g ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rwa [mul_inv_eq_iff_eq_mul] at hgx_eq
  have hgL : g ∈ Subgroup.normalizer (L : Set G) :=
    qTwoLMFrameC_normalizer_of_centralizer F hG (by omega) hVT g hgx
  let W : Subgroup (MulAut ↥L) := (ggGamma L F.hN).range
  have hγmem : ∀ b : ↥Bs, ggGamma L F.hN b ∈ W := fun b => ⟨b, rfl⟩
  let c : MulAut ↥L := ggConjAut L hgL
  have hcW : c ∈ Subgroup.normalizer (W : Set (MulAut ↥L)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : W.map (MulAut.conj c).toMonoidHom ≤ W := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨b, rfl⟩ := hw
      refine ⟨⟨g * b * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgBs b).mp b.2⟩, ?_⟩
      have hconjc : (MulAut.conj c).toMonoidHom (ggGamma L F.hN b)
          = c * ggGamma L F.hN b * c⁻¹ := by
        simpa using MulAut.conj_apply c (ggGamma L F.hN b)
      rw [hconjc]
      exact (qTwoLMDivStab_gamma_conj F hgBs hgL b).symm
    have hcard : Nat.card ↥(W.map (MulAut.conj c).toMonoidHom) = Nat.card ↥W :=
      Subgroup.card_map_of_injective (MulAut.conj c).injective
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
  let β : MulAut ↥W := ggConjAut W hcW
  let ψ : MulAut (QTwoQm m) := MulAut.congr F.theta.symm β
  have hψconj : ∀ σ : Equiv.Perm (Fin m), ∃ σ' : Equiv.Perm (Fin m),
      ψ * F.permV σ * ψ⁻¹ = F.permV σ' := by
    intro σ
    obtain ⟨n, hn, hnh⟩ := F.perm_ind σ
    have hn₁L : g * (n : G) * g⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hgL (n : G)).mp n.2
    let n₁ : ↥L := ⟨g * (n : G) * g⁻¹, hn₁L⟩
    have hconj : MulAut.conj n₁ = c * MulAut.conj n * c⁻¹ := by
      ext l
      rw [show c = ggConjAut L hgL from rfl]
      rw [MulAut.mul_apply, MulAut.mul_apply]
      rw [qTwoLMDivStab_ggConjAut_inv_apply hgL l, ggConjAut_apply, MulAut.conj_apply,
        MulAut.conj_apply]
      push_cast
      dsimp only [n₁]
      group
    have hn₁W : MulAut.conj n₁ ∈ Subgroup.normalizer (W : Set (MulAut ↥L)) := by
      rw [hconj]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcW hn) (Subgroup.inv_mem _ hcW)
    have hβconj : β * ggConjAut W hn * β⁻¹ = ggConjAut W hn₁W := by
      have hab : c * MulAut.conj n * c⁻¹ ∈
          Subgroup.normalizer (W : Set (MulAut ↥L)) := by
        rw [← hconj]
        exact hn₁W
      have h := qTwoLMDivStab_ggConjAut_mul_inv hcW hn hab
      have h2 : ggConjAut W hab = ggConjAut W hn₁W :=
        qTwoLMDivStab_ggConjAut_eq_of_eq hab hn₁W hconj.symm
      rw [show β = ggConjAut W hcW from rfl, h, h2]
    obtain ⟨π', hπ'⟩ := F.norm_perm n₁ hn₁W
    refine ⟨π', ?_⟩
    have hperm : F.permV σ = MulAut.congr F.theta.symm (ggConjAut W hn) := by
      rw [hnh]
      change F.permV σ = (MulAut.congr F.theta).symm (MulAut.congr F.theta (F.permV σ))
      rw [MulEquiv.symm_apply_apply]
    have hmain : ψ * F.permV σ * ψ⁻¹ =
        MulAut.congr F.theta.symm (β * ggConjAut W hn * β⁻¹) := by
      dsimp only [ψ]
      rw [hperm]
      simp only [map_mul, map_inv]
    rw [hmain, hβconj, hπ']
    change (MulAut.congr F.theta).symm (MulAut.congr F.theta (F.permV π')) = F.permV π'
    rw [MulEquiv.symm_apply_apply]
  let T : Subgroup ↥Bs := (Bs ⊓ L).subgroupOf Bs
  let γW : ↥Bs →* ↥W := (ggGamma L F.hN).codRestrict W (fun b => hγmem b)
  let f : ↥Bs →* QTwoQm m := F.theta.symm.toMonoidHom.comp γW
  let U : Subgroup (QTwoQm m) := Subgroup.map f T
  have hUstab : ∀ (σ : Equiv.Perm (Fin m)) (u : QTwoQm m), u ∈ U → F.permV σ u ∈ U := by
    intro σ u hu
    change u ∈ Subgroup.map f T at hu
    change F.permV σ u ∈ Subgroup.map f T
    rw [Subgroup.mem_map] at hu ⊢
    obtain ⟨b, hbT, hb⟩ := hu
    obtain ⟨n, hn, hnh⟩ := F.perm_ind σ
    obtain ⟨n', hn'Bs, hn'conj⟩ := F.link n hn
    have hn'W : MulAut.conj n' ∈ Subgroup.normalizer (W : Set (MulAut ↥L)) := by
      rw [hn'conj]
      exact hn
    have hnb : (n' : G) * (b : G) * (n' : G)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp hn'Bs b).mp b.2
    let b' : ↥Bs := ⟨(n' : G) * (b : G) * (n' : G)⁻¹, hnb⟩
    have hb'L : (b' : G) ∈ L := by
      have hbL : (b : G) ∈ (Bs ⊓ L) := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hbT)
      exact mul_mem (mul_mem n'.2 hbL.2) (inv_mem n'.2)
    refine ⟨b', Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hnb, hb'L⟩), ?_⟩
    have hθ : F.theta (f b) = ⟨ggGamma L F.hN b, hγmem b⟩ := by
      simp [f, γW]
    have hθ' : F.theta (f b') = ⟨ggGamma L F.hN b', hγmem b'⟩ := by
      simp [f, γW]
    have hβγ : ggConjAut W hn'W ⟨ggGamma L F.hN b, hγmem b⟩ =
        ⟨ggGamma L F.hN b', hγmem b'⟩ := by
      apply Subtype.ext
      have h := qTwoLMDivStab_ggConjAut_gamma F hn'W hn'Bs b
      exact h
    have hstep : F.theta (F.permV σ u) = F.theta (f b') := by
      rw [← hb, hθ']
      calc F.theta (F.permV σ (f b))
          = (MulAut.congr F.theta (F.permV σ)) (F.theta (f b)) := by
              simp [MulAut.congr_apply]
        _ = ggConjAut W hn (F.theta (f b)) := by rw [hnh]
        _ = ggConjAut W hn ⟨ggGamma L F.hN b, hγmem b⟩ := by rw [hθ]
        _ = ggConjAut W hn'W ⟨ggGamma L F.hN b, hγmem b⟩ := by
              rw [qTwoLMDivStab_ggConjAut_eq_of_eq hn hn'W hn'conj.symm]
        _ = ⟨ggGamma L F.hN b', hγmem b'⟩ := hβγ
    exact (F.theta.injective hstep).symm
  have hfixU : ∀ u ∈ U, ψ u = u := by
    intro u hu
    change u ∈ Subgroup.map f T at hu
    rw [Subgroup.mem_map] at hu
    obtain ⟨b, hbT, rfl⟩ := hu
    have hbL : (b : G) ∈ L :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hbT)).2
    have hδb : δ b = b := hδT b hbL
    have hgb : g * (b : G) * g⁻¹ = (b : G) := by
      have h1 : ((δ b : ↥Bs) : G) = (b : G) := by rw [hδb]
      rw [hδeq, ggConjAut_apply] at h1
      exact h1
    have hθ : F.theta (f b) = ⟨ggGamma L F.hN b, hγmem b⟩ := by
      simp [f, γW]
    have hβfix : β ⟨ggGamma L F.hN b, hγmem b⟩ =
        ⟨ggGamma L F.hN b, hγmem b⟩ := by
      apply Subtype.ext
      rw [show β = ggConjAut W hcW from rfl, ggConjAut_apply]
      rw [qTwoLMDivStab_gamma_conj F hgBs hgL b]
      rw [show (⟨g * (b : G) * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp hgBs b).mp b.2⟩ : ↥Bs) = b from Subtype.ext hgb]
    have hψ : ψ (f b) = F.theta.symm (β (F.theta (f b))) := by
      simp [ψ, MulAut.congr_apply]
    rw [hψ, hθ, hβfix]
    simp [f, γW]
  have hcardU : Nat.card (QTwoQm m) ≤ 3 * Nat.card U := by
    have hcardQm : Nat.card (QTwoQm m) = 3 ^ (m - 1) := qTwoLMDivStab_card_Qm m (by omega)
    have hcardT0 : Nat.card ↥(Bs ⊓ L) = 3 ^ (m - 1) := qTwoLMFrameC_card_T F hVT
    have hcardT : Nat.card ↥T = 3 ^ (m - 1) := by
      rw [← hcardT0]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hKle : Nat.card (f.comp T.subtype).ker ≤ 3 := by
      have hkerle : (f.comp T.subtype).ker ≤
          ((Subgroup.zpowers x).subgroupOf Bs).comap T.subtype := by
        intro t ht
        rw [Subgroup.mem_comap]
        change ((t.1 : ↥Bs) : G) ∈ Subgroup.zpowers x
        rw [← F.ker (t.1 : ↥Bs)]
        have ht' : f (t.1 : ↥Bs) = 1 := ht
        have h1 : γW (t.1 : ↥Bs) = 1 := by
          have h2 := congrArg F.theta ht'
          simpa [f] using h2
        have h3 : ((γW (t.1 : ↥Bs) : ↥W) : MulAut ↥L) = 1 := by rw [h1]; rfl
        simpa [γW] using h3
      have hdvd : Nat.card ↥(((Subgroup.zpowers x).subgroupOf Bs).comap T.subtype) ∣ 3 := by
        have h := Subgroup.card_comap_dvd_of_injective
          ((Subgroup.zpowers x).subgroupOf Bs) T.subtype T.subtype_injective
        rwa [show Nat.card ↥((Subgroup.zpowers x).subgroupOf Bs) = 3 by
          rw [Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr F.hx)).toEquiv,
            Nat.card_zpowers, F.hord]] at h
      calc Nat.card (f.comp T.subtype).ker
          ≤ Nat.card ↥(((Subgroup.zpowers x).subgroupOf Bs).comap T.subtype) :=
            Subgroup.card_le_of_le hkerle
        _ ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hrange : (f.comp T.subtype).range = U := by
      change (f.comp T.subtype).range = Subgroup.map f T
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hcard := Subgroup.card_ker_mul_card_range (f.comp T.subtype)
    rw [hrange] at hcard
    rw [hcardQm]
    calc 3 ^ (m - 1) = Nat.card ↥T := hcardT.symm
      _ = Nat.card (f.comp T.subtype).ker * Nat.card U := hcard.symm
      _ ≤ 3 * Nat.card U := by
          exact Nat.mul_le_mul_right _ hKle
  have hψ1 : ψ = 1 := hrigid U hUstab hcardU ψ hψconj hfixU
  have hβ1 : β = 1 := by
    have h := congrArg (MulAut.congr F.theta) hψ1
    have h1 : MulAut.congr F.theta (MulAut.congr F.theta.symm β) = β := by
      change (MulAut.congr F.theta) ((MulAut.congr F.theta).symm β) = β
      rw [MulEquiv.apply_symm_apply]
    rw [h1] at h
    have h2 : MulAut.congr F.theta (1 : MulAut (QTwoQm m)) = 1 :=
      MulEquiv.map_one (MulAut.congr F.theta)
    rw [h2] at h
    exact h
  have hfixW : ∀ w : ↥W, β w = w := by
    intro w
    rw [hβ1]
    rfl
  have hker : ∀ b : ↥Bs, (δ b) * b⁻¹ ∈ (Subgroup.zpowers x).subgroupOf Bs := by
    intro b
    rw [Subgroup.mem_subgroupOf]
    have hγeq : ggGamma L F.hN ⟨g * b * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp hgBs b).mp b.2⟩ = ggGamma L F.hN b := by
      have hfixb := hfixW ⟨ggGamma L F.hN b, hγmem b⟩
      have h1 : ((β ⟨ggGamma L F.hN b, hγmem b⟩ : ↥W) : MulAut ↥L) =
          (⟨ggGamma L F.hN b, hγmem b⟩ : ↥W) := by rw [hfixb]
      rw [show β = ggConjAut W hcW from rfl, ggConjAut_apply] at h1
      rw [qTwoLMDivStab_gamma_conj F hgBs hgL b] at h1
      exact h1
    have hmem : ggGamma L F.hN
        (⟨g * b * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgBs b).mp b.2⟩ * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hγeq, mul_inv_cancel]
    have hmem' := (F.ker (⟨g * b * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp hgBs b).mp b.2⟩ * b⁻¹)).mp hmem
    have hδb : ((δ b : ↥Bs) : G) = g * (b : G) * g⁻¹ := hgδ b
    have heq : (⟨g * (b : G) * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp hgBs b).mp b.2⟩ : ↥Bs) = δ b :=
      Subtype.ext hδb.symm
    rw [heq] at hmem'
    simpa using hmem'
  by_contra hδne
  let H : Subgroup ↥Bs :=
    { carrier := {b | δ b = b}
      one_mem' := map_one δ
      mul_mem' := by
        intro a b ha hb
        change δ (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        change δ a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hcardT0 : Nat.card ↥(Bs ⊓ L) = 3 ^ (m - 1) := qTwoLMFrameC_card_T F hVT
  have hcardT : Nat.card ↥T = 3 ^ (m - 1) := by
    rw [← hcardT0]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcardBs : Nat.card ↥Bs = 3 ^ m := qTwoLMDivStab_card_Bs F (by omega) hV
  have hTindex : T.index = 3 := by
    have h := Subgroup.card_mul_index T
    rw [hcardT, hcardBs] at h
    have hpow : 3 ^ m = 3 ^ (m - 1) * 3 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hTleH : T ≤ H := by
    intro t ht
    have htL : (t : G) ∈ L := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ht)).2
    exact hδT t htL
  have hHne : H ≠ ⊤ := by
    intro htop
    apply hδne
    ext b
    have hbH : b ∈ H := by rw [htop]; exact Subgroup.mem_top b
    simpa [H] using hbH
  have hH_eq_T : H = T := by
    have h1 : T.relIndex H * H.relIndex ⊤ = T.relIndex ⊤ :=
      Subgroup.relIndex_mul_relIndex (H := T) (K := H) (L := ⊤) hTleH le_top
    have hTrel : T.relIndex ⊤ = 3 := by
      rw [Subgroup.relIndex_top_right, hTindex]
    rw [hTrel] at h1
    have hHrel_dvd : H.relIndex ⊤ ∣ 3 := ⟨T.relIndex H, by rw [mul_comm]; exact h1.symm⟩
    have hHrel_ne : H.relIndex ⊤ ≠ 1 := by
      intro h
      apply hHne
      exact top_le_iff.mp (Subgroup.relIndex_eq_one.mp h)
    have hHrel : H.relIndex ⊤ = 3 := by
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (H.relIndex ⊤) hHrel_dvd with h | h
      · exact absurd h hHrel_ne
      · exact h
    have hTrelH : T.relIndex H = 1 := by
      rw [hHrel] at h1
      have h' : T.relIndex H * 3 = 1 * 3 := by simpa using h1
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hTrelH) hTleH
  have hfixcard : Nat.card {b : ↥Bs // δ b = b} * 3 = Nat.card ↥Bs := by
    have hcard : Nat.card ↥T * T.index = Nat.card ↥Bs := Subgroup.card_mul_index T
    rw [hTindex, ← hH_eq_T] at hcard
    change Nat.card ↥H * 3 = Nat.card ↥Bs
    exact hcard
  have htrans : GGIsTransvection 3 δ := by
    refine ⟨hfixcard, fun b => ?_⟩
    have hmem : (b⁻¹ * δ b : ↥Bs) ∈ (Subgroup.zpowers x).subgroupOf Bs := by
      refine Subgroup.mem_subgroupOf.mpr ?_
      have hkb : ((δ b * b⁻¹ : ↥Bs) : G) ∈ Subgroup.zpowers x :=
        Subgroup.mem_subgroupOf.mp (hker b)
      have hcomm := F.elemAb.comm (b⁻¹).2 (δ b).2
      have h1 : ((b⁻¹ * δ b : ↥Bs) : G) = ((δ b * b⁻¹ : ↥Bs) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact hcomm
      rwa [h1]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hmem)
    have hxk : (⟨x, F.hx⟩ : ↥Bs) ^ k = b⁻¹ * δ b := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hk
    rw [← hxk, map_zpow, hδx]
  exact hrt.1.2.2.2.1 δ hδI htrans

end CFSG.StandardType.QTwo

end
