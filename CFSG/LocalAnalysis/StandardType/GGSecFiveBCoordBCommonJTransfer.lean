module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TransferData
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGTCJDescent
import CFSG.GroupTheory.InnerCentralizerProjection
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace CommonJ

variable {G : Type} [Group G] {L : Subgroup G} {R : Type} [Group R]

@[expose] def GGGammaHatSpec (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {Bs : Subgroup G}
    (γ : ↥Bs →* R) : Prop :=
  ∀ (b : ↥Bs) (l l' : ↥L), (l' : G) = b * l * (b : G)⁻¹ →
    ggQuotHom θ l' = γ b * ggQuotHom θ l * (γ b)⁻¹

private theorem gammaHatSpec_unique {θ : ↥L ⧸ Subgroup.center ↥L ≃* R}
    (hR : Subgroup.center R = ⊥) {Bs : Subgroup G} (b : ↥Bs)
    (hN : ∀ l : ↥L, ∃ l' : ↥L, (l' : G) = b * l * (b : G)⁻¹) {h₁ h₂ : R}
    (h₁s : ∀ (l l' : ↥L), (l' : G) = b * l * (b : G)⁻¹ →
      ggQuotHom θ l' = h₁ * ggQuotHom θ l * h₁⁻¹)
    (h₂s : ∀ (l l' : ↥L), (l' : G) = b * l * (b : G)⁻¹ →
      ggQuotHom θ l' = h₂ * ggQuotHom θ l * h₂⁻¹) :
    h₁ = h₂ := by
  have hcen : h₂⁻¹ * h₁ ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ r
    obtain ⟨l', hl'⟩ := hN l
    have e₁ := h₁s l l' hl'
    have e₂ := h₂s l l' hl'
    have heq : h₁ * ggQuotHom θ l * h₁⁻¹ = h₂ * ggQuotHom θ l * h₂⁻¹ :=
      e₁.symm.trans e₂
    calc
      ggQuotHom θ l * (h₂⁻¹ * h₁)
          = h₂⁻¹ * (h₂ * ggQuotHom θ l * h₂⁻¹) * h₁ := by group
      _ = h₂⁻¹ * (h₁ * ggQuotHom θ l * h₁⁻¹) * h₁ := by rw [← heq]
      _ = (h₂⁻¹ * h₁) * ggQuotHom θ l := by group
  have hz : h₂⁻¹ * h₁ = 1 := by
    have h := hcen
    rw [hR] at h
    simpa using h
  exact (inv_mul_eq_one.mp hz).symm

theorem exists_gammaHat (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (hR : Subgroup.center R = ⊥)
    {Bs : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hinn : ∀ b ∈ Bs, ∃ h : R, ∀ l l' : ↥L, (l' : G) = b * l * b⁻¹ →
      ggQuotHom θ l' = h * ggQuotHom θ l * h⁻¹) :
    ∃ γ : ↥Bs →* R, GGGammaHatSpec θ γ := by
  classical
  let f : ↥Bs → R := fun b => Classical.choose (hinn b b.2)
  have hf_spec : ∀ (b : ↥Bs) (l l' : ↥L), (l' : G) = b * l * (b : G)⁻¹ →
      ggQuotHom θ l' = f b * ggQuotHom θ l * (f b)⁻¹ :=
    fun b => Classical.choose_spec (hinn b b.2)
  have hf_one : f 1 = 1 := by
    refine gammaHatSpec_unique hR 1 (fun l => ⟨⟨(1 : G) * (l : G) * (1 : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hBsN (1 : ↥Bs).2) l).mp l.2⟩, rfl⟩) (hf_spec 1) ?_
    intro l l' h
    have hl : l' = l := Subtype.ext (by simpa using h)
    subst hl
    simp
  have hf_mul : ∀ b₁ b₂ : ↥Bs, f (b₁ * b₂) = f b₁ * f b₂ := by
    intro b₁ b₂
    refine gammaHatSpec_unique hR (b₁ * b₂) (fun l => ⟨⟨(b₁ * b₂ : G) * (l : G) * ((b₁ * b₂ : G))⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hBsN (b₁ * b₂).2) l).mp l.2⟩, rfl⟩) (hf_spec (b₁ * b₂)) ?_
    intro l l' h
    let l₂ : ↥L := ⟨(b₂ : G) * l * (b₂ : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hBsN b₂.2) l).mp l.2⟩
    have hl₂ : (l₂ : G) = (b₂ : G) * l * (b₂ : G)⁻¹ := rfl
    have h' : (l' : G) = (b₁ : G) * l₂ * (b₁ : G)⁻¹ := by
      rw [h, hl₂]
      simp only [Subgroup.coe_mul]
      group
    have e₁ := hf_spec b₁ l₂ l' h'
    have e₂ := hf_spec b₂ l l₂ hl₂
    rw [e₁, e₂]
    group
  let γ : ↥Bs →* R :=
    { toFun := f
      map_one' := hf_one
      map_mul' := hf_mul }
  refine ⟨γ, ?_⟩
  intro b l l' h
  exact hf_spec b l l' h

theorem gammaHat_conj {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} (hR : Subgroup.center R = ⊥)
    {Bs : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) {γ : ↥Bs →* R}
    (hγ : GGGammaHatSpec θ γ) (g : ↥L) (b b' : ↥Bs) (hb' : (b' : G) = g * b * (g : G)⁻¹) :
    γ b' = ggQuotHom θ g * γ b * (ggQuotHom θ g)⁻¹ := by
  refine gammaHatSpec_unique hR b' (fun l => ⟨⟨(b' : G) * (l : G) * (b' : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hBsN b'.2) l).mp l.2⟩, rfl⟩) (hγ b') ?_
  intro l l' h
  let l₁ : ↥L := ⟨(g : G)⁻¹ * l * (g : G), L.mul_mem (L.mul_mem (L.inv_mem g.2) l.2) g.2⟩
  have hl₁ : (l₁ : G) = (g : G)⁻¹ * l * (g : G) := rfl
  let m : ↥L := ⟨(b : G) * l₁ * (b : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hBsN b.2) l₁).mp l₁.2⟩
  have hm : (m : G) = (b : G) * l₁ * (b : G)⁻¹ := rfl
  have h' : (l' : G) = (g : G) * m * (g : G)⁻¹ := by
    rw [h, hb', hm, hl₁]
    group
  have hgl : ggQuotHom θ l' = ggQuotHom θ g * ggQuotHom θ m * (ggQuotHom θ g)⁻¹ := by
    have hl' : l' = g * m * g⁻¹ := Subtype.ext h'
    rw [hl', map_mul, map_mul, map_inv]
  have hgl₁ : ggQuotHom θ l₁ = (ggQuotHom θ g)⁻¹ * ggQuotHom θ l * ggQuotHom θ g := by
    have hl : l₁ = g⁻¹ * l * g := Subtype.ext hl₁
    rw [hl, map_mul, map_mul, map_inv]
  have e := hγ b l₁ m hm
  rw [hgl, e, hgl₁]
  group

section Config

variable [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {D J : Subgroup G}
  {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {γ : ↥Bs →* R}

theorem gammaHat_eq_one_iff (hcfg : GGConfig p B Bs x L D J) (hB : B = Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hR : Subgroup.center R = ⊥)
    (hγ : GGGammaHatSpec θ γ) (b : ↥Bs) : γ b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hSB : LargeEvenSStar p Bs x L := hB ▸ hS
  have hLperf : commutator ↥L = ⊤ := hS.2.2.2.1.2.2.1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_of_le_centralizer hS.2.2.2.1.1
  constructor
  · intro hγb
    have hβ : ggBeta L θ hBsN b = 1 := by
      ext r
      obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ r
      rw [MulAut.one_apply, ggBeta_eq]
      change ggLAut L θ ⟨(b : G), hBsN b.2⟩ (ggQuotHom θ l) = ggQuotHom θ l
      rw [ggQuotHom_apply, ggLAut_apply]
      let l' : ↥L := ⟨(b : G) * l * (b : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hBsN b.2) l).mp l.2⟩
      have hval : (L.normalizerMonoidHom ⟨(b : G), hBsN b.2⟩ l : ↥L) = l' := rfl
      have hspec := hγ b l l' rfl
      rw [hγb] at hspec
      rw [hval]
      simpa [ggQuotHom_apply] using hspec
    exact (ggBeta_eq_one_iff L θ hp hSB hLperf hBsN b).mp hβ
  · intro hbz
    have hbC : (b : G) ∈ Subgroup.centralizer (L : Set G) :=
      (Subgroup.zpowers_le.mpr hxC) hbz
    have hcen : γ b ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ r
      let l' : ↥L := ⟨(b : G) * l * (b : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hBsN b.2) l).mp l.2⟩
      have hl' : l' = l := by
        refine Subtype.ext ?_
        have hcomm := Subgroup.mem_centralizer_iff.mp hbC l l.2
        calc
          (b : G) * l * (b : G)⁻¹ = l * (b : G) * (b : G)⁻¹ := by rw [hcomm]
          _ = l := by group
      have hspec := hγ b l l' rfl
      rw [hl'] at hspec
      have hcomm : γ b * ggQuotHom θ l = ggQuotHom θ l * γ b := by
        calc
          γ b * ggQuotHom θ l = (γ b * ggQuotHom θ l * (γ b)⁻¹) * γ b := by group
          _ = ggQuotHom θ l * γ b := by rw [← hspec]
      exact hcomm.symm
    have h1 : γ b = 1 := by
      have h := hcen
      rw [hR] at h
      simpa using h
    exact h1

theorem card_range_gammaHat (hcfg : GGConfig p B Bs x L D J) (hB : B = Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hR : Subgroup.center R = ⊥)
    (hγ : GGGammaHatSpec θ γ) {n : ℕ} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) :
    Nat.card γ.range = p ^ (n - 1) := by
  classical
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hSB : LargeEvenSStar p Bs x L := hB ▸ hS
  have hcardBs : Nat.card ↥Bs = p ^ n := by
    calc
      Nat.card ↥Bs = Nat.card (Fin n → Multiplicative (ZMod p)) := Nat.card_congr eta.toEquiv
      _ = Nat.card (Multiplicative (ZMod p)) ^ n := by rw [Nat.card_fun, Nat.card_fin]
      _ = p ^ n := by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hker : ∀ b : ↥Bs, γ b = 1 ↔ (b : G) ∈ Subgroup.zpowers x :=
    gammaHat_eq_one_iff hcfg hB hBsN hR hγ
  have hkercard : Nat.card ↥γ.ker = p := by
    have hker_eq : γ.ker = (Subgroup.zpowers x).subgroupOf Bs := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker b]
    rw [hker_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hSB.2.1)).toEquiv,
      Nat.card_zpowers]
    exact orderOf_eq_prime (hSB.1.1.2 x hSB.2.1) hSB.2.2.1
  have hn0 : n ≠ 0 := by
    intro hn
    have h2 : 2 ≤ Nat.card ↥Bs := by
      haveI : Nontrivial ↥Bs :=
        ⟨⟨⟨x, hSB.2.1⟩, ⟨1, Bs.one_mem⟩, by
          intro h
          exact hSB.2.2.1 (congrArg Subtype.val h)⟩⟩
      exact Finite.one_lt_card
    rw [hn, pow_zero] at hcardBs
    omega
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hm
  have hmul := Subgroup.card_ker_mul_card_range γ
  rw [hkercard, hcardBs, pow_succ] at hmul
  have hpow : p * Nat.card γ.range = p * p ^ m := by
    rw [hmul, mul_comm (p ^ m) p]
  have hrange : Nat.card γ.range = p ^ m := Nat.eq_of_mul_eq_mul_left hp.pos hpow
  simpa using hrange

theorem isComponentOf_map_J (hcfg : GGConfig p B Bs x L D J) (hB : B = Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hR : Subgroup.center R = ⊥)
    (hγ : GGGammaHatSpec θ γ) {z : ↥Bs} (hzD : (z : G) ∈ D)
    (hzx : (z : G) ∉ Subgroup.zpowers x) :
    CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map (ggQuotHom θ))
      (Subgroup.centralizer ({γ z} : Set R)) := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hSB : LargeEvenSStar p Bs x L := hB ▸ hS
  have hpre : LargeEvenStdSubPre p B x L D J := hcfg.2.2.1
  have hDgen : Subgroup.closure {x, (z : G)} = D :=
    l02qj12_closure_pair_eq_of_card hp hpre.2.2.2.1 hS.2.2.1 hpre.2.1 hpre.2.2.1 hzD hzx
  have hCD : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({(z : G)} : Set G) :=
    l02qj12_inf_centralizer_eq hDgen hS.2.2.2.1.1
  have hJc : CFSG.Assembly.IsComponentOf J
      (L ⊓ Subgroup.centralizer ({(z : G)} : Set G)) := by
    rw [← hCD]
    exact hpre.2.2.2.2.2.1
  have hzN : (z : G) ∈ Subgroup.normalizer (L : Set G) := hBsN z.2
  have hJfix : CFSG.Assembly.IsComponentOf (J.subgroupOf L)
      (ggFixSub (L.normalizerMonoidHom ⟨(z : G), hzN⟩)) :=
    ggIsComponentOf_ggFixSub_normalizerMonoidHom hzN hJc
  let e : MulAut ↥L := L.normalizerMonoidHom ⟨(z : G), hzN⟩
  let φ : MulAut R := MulAut.conj (γ z)
  have hφ : ∀ l : ↥L, φ (ggQuotHom θ l) = ggQuotHom θ (e l) := by
    intro l
    have hval : ((e l : ↥L) : G) = (z : G) * (l : G) * (z : G)⁻¹ := rfl
    have hspec := hγ z l (e l) hval
    rw [MulAut.conj_apply]
    exact hspec.symm
  have hdescent := TCJ.ggTCJ_descent (ψ := ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) e φ hφ (J.subgroupOf L) hJfix
  have hfix : ggFixSub φ = Subgroup.centralizer ({γ z} : Set R) := by
    ext r
    rw [mem_ggFixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
      mul_inv_eq_iff_eq_mul]
    exact eq_comm
  simpa [hfix] using hdescent.1

theorem card_range_inf_centralizer_J (hcfg : GGConfig p B Bs x L D J) (hB : B = Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hR : Subgroup.center R = ⊥)
    (hγ : GGGammaHatSpec θ γ) :
    Nat.card ↥(γ.range ⊓
      Subgroup.centralizer (((J.subgroupOf L).map (ggQuotHom θ) : Subgroup R) : Set R)) = p := by
  classical
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hSB : LargeEvenSStar p Bs x L := hB ▸ hS
  have hpre : LargeEvenStdSubPre p B x L D J := hcfg.2.2.1
  have hJc : CFSG.Assembly.IsComponentOf J
      (L ⊓ Subgroup.centralizer (D : Set G)) := hpre.2.2.2.2.2.1
  have hJL : J ≤ L := hJc.1.trans inf_le_left
  have hJperf : Group.IsPerfect ↥J := ⟨hJc.2.2.1⟩
  have hDeq : D = B ⊓ Subgroup.centralizer (J : Set G) := hpre.2.2.2.2.2.2
  have hDBs : D ≤ Bs := hB ▸ hpre.1
  have hDC : D ≤ Subgroup.centralizer (J : Set G) := hDeq.le.trans inf_le_right
  have hBsE : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hcommBs : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    TableB.IsElemAbelian.comm hBsE ha hb
  have hBsNJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcommBs hcfg.2.1.1 hpre hBsN
  let E : Subgroup ↥Bs := D.subgroupOf Bs
  have hγD_le : E.map γ ≤ γ.range ⊓
      Subgroup.centralizer (((J.subgroupOf L).map (ggQuotHom θ) : Subgroup R) : Set R) := by
    refine le_inf ?_ ?_
    · rintro r ⟨e, -, rfl⟩
      exact ⟨e, rfl⟩
    · intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hr
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hy
      have heD : (e : G) ∈ D := Subgroup.mem_subgroupOf.mp he
      have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
      have heC : (e : G) ∈ Subgroup.centralizer (J : Set G) := hDC heD
      have hej : (j : G) * (e : G) = (e : G) * (j : G) :=
        Subgroup.mem_centralizer_iff.mp heC j hjJ
      have hej' : (e : G) * (j : G) * (e : G)⁻¹ = (j : G) := by
        rw [← hej]
        group
      have hspec := hγ e j j (by simpa using hej'.symm)
      have hcomm : ggQuotHom θ j * γ e = γ e * ggQuotHom θ j := by
        calc
          ggQuotHom θ j * γ e =
              (γ e * ggQuotHom θ j * (γ e)⁻¹) * γ e := congrArg (· * γ e) hspec
          _ = γ e * ggQuotHom θ j := by group
      exact hcomm
  have hinf_le : γ.range ⊓
      Subgroup.centralizer (((J.subgroupOf L).map (ggQuotHom θ) : Subgroup R) : Set R) ≤
        E.map γ := by
    rintro r ⟨⟨b, rfl⟩, hrC⟩
    have hbJ : (b : G) ∈ Subgroup.normalizer (J : Set G) := hBsNJ b.2
    have hbC : (b : G) ∈ Subgroup.centralizer (J : Set G) := by
      refine CFSG.mem_centralizer_of_commutator_mem_center hJperf hbJ ?_
      intro j hj
      have hbJj : (b : G) * j * (b : G)⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp hbJ j).mp hj
      have hmemJ : (b : G) * j * (b : G)⁻¹ * j⁻¹ ∈ J :=
        J.mul_mem hbJj (J.inv_mem hj)
      let jL : ↥L := ⟨j, hJL hj⟩
      let bjL : ↥L := ⟨(b : G) * j * (b : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hBsN b.2) jL).mp jL.2⟩
      have hspec := hγ b jL bjL rfl
      have hcomm := Subgroup.mem_centralizer_iff.mp hrC (ggQuotHom θ jL)
        (Subgroup.mem_map_of_mem (ggQuotHom θ) (Subgroup.mem_subgroupOf.mpr hj))
      have hψ : ggQuotHom θ bjL = ggQuotHom θ jL := by
        rw [hspec]
        calc
          γ b * ggQuotHom θ jL * (γ b)⁻¹ = (ggQuotHom θ jL * γ b) * (γ b)⁻¹ := by
            rw [← hcomm]
          _ = ggQuotHom θ jL := by group
      have hmemZ : bjL * jL⁻¹ ∈ Subgroup.center ↥L := by
        rw [← ker_ggQuotHom θ, MonoidHom.mem_ker, map_mul, map_inv, hψ, mul_inv_cancel]
      have hcentJ : (⟨(b : G) * j * (b : G)⁻¹ * j⁻¹, hmemJ⟩ : ↥J) ∈
          Subgroup.center ↥J := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        have hzy := Subgroup.mem_center_iff.mp hmemZ ⟨(y : G), hJL y.2⟩
        have hzy' := congrArg (fun w : ↥L => (w : G)) hzy
        simpa only [bjL, jL, Subgroup.coe_mul, Subgroup.coe_inv] using hzy'
      exact Subgroup.mem_map_of_mem J.subtype hcentJ
    have hbD : (b : G) ∈ D := by
      rw [hDeq]
      exact ⟨hB ▸ b.2, hbC⟩
    exact Subgroup.mem_map.mpr ⟨b, Subgroup.mem_subgroupOf.mpr hbD, rfl⟩
  have hinf_eq : γ.range ⊓
      Subgroup.centralizer (((J.subgroupOf L).map (ggQuotHom θ) : Subgroup R) : Set R) =
        E.map γ := le_antisymm hinf_le hγD_le
  have hEcard : Nat.card ↥E = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDBs).toEquiv, hpre.2.2.1]
  let X : Subgroup ↥Bs := (Subgroup.zpowers x).subgroupOf Bs
  have hxE : x ∈ D := hpre.2.2.2.1
  have hXE : X ≤ E := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact Subgroup.zpowers_le.mpr hxE hy
  let φ : ↥E →* R := γ.comp E.subtype
  have hφrange : φ.range = E.map γ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hφker : Nat.card ↥φ.ker = p := by
    have hker_eq : φ.ker = X.subgroupOf E := by
      ext e
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf]
      exact gammaHat_eq_one_iff hcfg hB hBsN hR hγ (e : ↥Bs)
    rw [hker_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXE).toEquiv]
    change Nat.card ↥((Subgroup.zpowers x).subgroupOf Bs) = p
    rw [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hSB.2.1)).toEquiv,
      Nat.card_zpowers]
    exact orderOf_eq_prime (hS.1.1.2 x hS.2.1) hS.2.2.1
  have hrangecard : Nat.card ↥(E.map γ) = p := by
    have hmul := Subgroup.card_ker_mul_card_range φ
    rw [hφker, hEcard] at hmul
    have h2 : p * Nat.card φ.range = p * p := by
      simpa [pow_two] using hmul
    have h3 : Nat.card φ.range = p := Nat.eq_of_mul_eq_mul_left hp.pos h2
    rwa [hφrange] at h3
  rw [hinf_eq]
  exact hrangecard

variable (θ) in
theorem nonempty_centerQuot_J (hcfg : GGConfig p B Bs x L D J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      ↥((J.subgroupOf L).map (ggQuotHom θ)) ⧸
        Subgroup.center ↥((J.subgroupOf L).map (ggQuotHom θ))) := by
  classical
  have hpre : LargeEvenStdSubPre p B x L D J := hcfg.2.2.1
  have hJc : CFSG.Assembly.IsComponentOf J
      (L ⊓ Subgroup.centralizer (D : Set G)) := hpre.2.2.2.2.2.1
  have hJL : J ≤ L := hJc.1.trans inf_le_left
  have hJperf : Group.IsPerfect ↥J := ⟨hJc.2.2.1⟩
  let e : ↥J ≃* ↥(J.subgroupOf L) := (Subgroup.subgroupOfEquivOfLe hJL).symm
  let φ : ↥J →* ↥((J.subgroupOf L).map (ggQuotHom θ)) :=
    ((ggQuotHom θ).subgroupMap (J.subgroupOf L)).comp e.toMonoidHom
  have hφsurj : Function.Surjective φ :=
    (MonoidHom.subgroupMap_surjective (ggQuotHom θ) (J.subgroupOf L)).comp e.surjective
  have hφker : φ.ker ≤ Subgroup.center ↥J := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hzψ : ggQuotHom θ ((e z : ↥(J.subgroupOf L)) : ↥L) = 1 :=
      congrArg Subtype.val hz
    have hzL : ((e z : ↥(J.subgroupOf L)) : ↥L) ∈ Subgroup.center ↥L := by
      rw [← ker_ggQuotHom θ]
      exact MonoidHom.mem_ker.mpr hzψ
    rw [Subgroup.mem_center_iff]
    intro w
    apply e.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hzL (e w)
  have hc := CFSG.LocalCores.comap_center_eq_of_perfect hJperf φ hφsurj hφker
  let g : (↥J ⧸ Subgroup.center ↥J) →*
      (↥((J.subgroupOf L).map (ggQuotHom θ)) ⧸
        Subgroup.center ↥((J.subgroupOf L).map (ggQuotHom θ))) :=
    QuotientGroup.map (Subgroup.center ↥J)
      (Subgroup.center ↥((J.subgroupOf L).map (ggQuotHom θ))) φ (le_of_eq hc.symm)
  have hginj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_map, hc]
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    simp [Subgroup.mem_map, QuotientGroup.eq_one_iff]
  have hgsurj : Function.Surjective g := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := hφsurj y
    exact ⟨QuotientGroup.mk x, rfl⟩
  exact ⟨MulEquiv.ofBijective g ⟨hginj, hgsurj⟩⟩

variable (θ) in
theorem nonempty_J_of_center_eq_bot (hcfg : GGConfig p B Bs x L D J)
    (hL : Subgroup.center ↥L = ⊥) :
    Nonempty (↥J ≃* ↥((J.subgroupOf L).map (ggQuotHom θ))) := by
  classical
  have hpre : LargeEvenStdSubPre p B x L D J := hcfg.2.2.1
  have hJc : CFSG.Assembly.IsComponentOf J
      (L ⊓ Subgroup.centralizer (D : Set G)) := hpre.2.2.2.2.2.1
  have hJL : J ≤ L := hJc.1.trans inf_le_left
  have hinj : Function.Injective (ggQuotHom θ) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_ggQuotHom, hL]
  exact ⟨(Subgroup.subgroupOfEquivOfLe hJL).symm.trans
    (Subgroup.equivMapOfInjective (J.subgroupOf L) (ggQuotHom θ) hinj)⟩

end Config

end CommonJ

end CFSG.StandardType

end
