module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Quasithin.H13.A5W1618m
public import CFSG.Quasithin.H13.A5W1618n

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

local notation "StSL" => Assembly.LowTwoRank.StatedSL

section General

variable {M : Type} [CommGroup M]

theorem le_fixV_of_perfect {N : Subgroup (MulAut M)} {W C : Subgroup M} (hp : ⁅N, N⁆ = N)
    (hC : ∀ g ∈ N, ∀ c ∈ C, g c = c) (hW : ∀ g ∈ N, ∀ w ∈ W, g w * w⁻¹ ∈ C) :
    W ≤ fixV N := by
  intro w hw
  rw [mem_fixV]
  intro g hg
  let f : ↥N →* M :=
    { toFun := fun h => (h : MulAut M) w * w⁻¹
      map_one' := by simp
      map_mul' := fun h₁ h₂ => by
        have hc : (h₁ : MulAut M) ((h₂ : MulAut M) w * w⁻¹) = (h₂ : MulAut M) w * w⁻¹ :=
          hC _ h₁.2 _ (hW _ h₂.2 w hw)
        have e : (h₁ : MulAut M) ((h₂ : MulAut M) w) =
            (h₂ : MulAut M) w * w⁻¹ * (h₁ : MulAut M) w := by
          rw [← hc, ← map_mul, inv_mul_cancel_right]
        show (h₁ : MulAut M) ((h₂ : MulAut M) w) * w⁻¹ =
          ((h₁ : MulAut M) w * w⁻¹) * ((h₂ : MulAut M) w * w⁻¹)
        rw [e, mul_comm ((h₂ : MulAut M) w * w⁻¹) ((h₁ : MulAut M) w), mul_right_comm] }
  have htop : commutator ↥N = ⊤ := Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hp)
  have hgc : (⟨g, hg⟩ : ↥N) ∈ commutator ↥N := by
    rw [htop]
    exact Subgroup.mem_top _
  have hk : (⟨g, hg⟩ : ↥N) ∈ f.ker := Abelianization.commutator_subset_ker f hgc
  exact mul_inv_eq_one.mp hk

theorem mem_fixV_of_mem_normalizer {N : Subgroup (MulAut M)} {n : MulAut M}
    (hn : n ∈ Subgroup.normalizer (N : Set (MulAut M))) {m : M} (hm : m ∈ fixV N) :
    n m ∈ fixV N :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer hn hm

end General

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem v12_mem_WK {K : Subgroup G} (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) :
    S.v12 ∈ S.WK K := by
  have hv : S.v12 ∈ S.Vv := S.mem_Vv.2 ⟨S.v12_mem_V, by rw [S.psi_v12]; decide +kernel⟩
  rw [S.Vv_eq_conjClosure] at hv
  rw [S.WK_eq hT]
  exact conjClosure_mono le_rfl (le_sup_right.trans le_sup_left) hv

theorem false_of_symmetricNatural (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} [IsMulCommutative ↥(S.WK K)] (hK : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {F : Type} [Field F] [Finite F]
    (hF4 : Nat.card F = 4) (e : ↥(S.plus K) ≃* ↥(StSL 2 F))
    {J G₁ : Subgroup (MulAut ↥(S.WK K))} {W₁ W₂ : Subgroup ↥(S.WK K)} (hNG₁ : S.plus K ≤ G₁)
    (hG₁J : G₁ ≤ J) (hW12 : W₁ ⊔ W₂ = ⊤) (hWi : W₁ ⊓ W₂ = fixV J) (hinv₂ : XMod.IsInv ↥J W₂)
    (hW₁ : W₁ = commV G₁ ⊔ fixV J) (hsym : SymmetricNatural G₁ W₁ (fixV J) 5) : False := by
  classical
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin 5) →* ↥G₁,
      (FFModel.symDn 5).RealizesVia G₁ W₁ (fixV J) π := hsym
  have hq := S.isQuasisimple_plus h1222 h517 hF hK hT
  obtain ⟨hp, -⟩ := qs_perfect_ne_bot hq
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hK.1 hT
  have hHKW : S.HK K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hR.2.1
  have hKHK : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hKW : K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hKHK.trans hHKW
  have hNH := S.HK_le_normalizer_plus h1222 h517 hF hK hT
  have hNJ : S.plus K ≤ J := hNG₁.trans hG₁J
  have hπi : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.symDn_faithful le_rfl) hπ
  set φ : Equiv.Perm (Fin 5) →* MulAut ↥(S.WK K) := G₁.subtype.comp π with hφdef
  have hφi : Function.Injective φ := G₁.subtype_injective.comp hπi
  have hNφ : S.plus K ≤ φ.range := by
    intro n hn
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 5), π σ = ⟨n, hNG₁ hn⟩ := hπ.1 ⟨n, hNG₁ hn⟩
    refine ⟨σ, ?_⟩
    show ((π σ : ↥G₁) : MulAut ↥(S.WK K)) = n
    rw [hσ]
  have h60 : Nat.card ↥(S.plus K) = 60 := by
    rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow (n := 2) (by rw [hF4]; norm_num)]
    norm_num
  have hA := comap_eq_alternatingGroup hφi hNφ hp h60
  have hAm : ∀ σ, φ σ ∈ S.plus K ↔ σ ∈ alternatingGroup (Fin 5) := fun σ => by
    rw [← hA, Subgroup.mem_comap]
  have hW₂N : W₂ ≤ fixV (S.plus K) := by
    refine le_fixV_of_perfect (C := fixV J) hp (fun g hg c hc => hc g (hNJ hg))
      fun g hg w hw => ?_
    have h1 : g w * w⁻¹ ∈ W₁ :=
      hW₁ ▸ Subgroup.mem_sup_left (Subgroup.subset_closure ⟨g, hNG₁ hg, w, rfl⟩)
    have h2 : g w * w⁻¹ ∈ W₂ := W₂.mul_mem (hinv₂ ⟨g, hNJ hg⟩ w hw) (W₂.inv_mem hw)
    rw [← hWi]
    exact ⟨h1, h2⟩
  have hW₂G : ∀ g ∈ G₁, ∀ w ∈ W₂, g w ∈ W₂ := fun g hg w hw => hinv₂ ⟨g, hG₁J hg⟩ w hw
  obtain ⟨Ψ, hΨs, hΨk, hΨe⟩ := exists_delta5_quot hπ hW12 hWi hW₂G
  have hΨe' : ∀ σ m, Ψ (φ σ m) = pact σ (Ψ m) := hΨe
  have hNW₂ : fixV (S.plus K) ≤ W₂ := by
    intro m hm
    rw [← hΨk]
    have hfix : ∀ σ ∈ alternatingGroup (Fin 5), pact σ (Ψ m) = Ψ m := fun σ hσ => by
      rw [← hΨe', hm _ ((hAm σ).mpr hσ)]
    exact eq_one_of_pact_c234_c3p _ (hfix _ (Equiv.Perm.mem_alternatingGroup.2 c234_sign))
      (hfix _ (Equiv.Perm.mem_alternatingGroup.2 c3p_sign))
  have hker : ∀ m, Ψ m = 1 ↔ m ∈ fixV (S.plus K) := fun m =>
    (hΨk m).trans ⟨fun h => hW₂N h, fun h => hNW₂ h⟩
  have hzW : S.z ∈ S.WK K := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  set zW : ↥(S.WK K) := ⟨S.z, hzW⟩ with hzWdef
  set vW : ↥(S.WK K) := ⟨S.v12, S.v12_mem_WK hT⟩ with hvWdef
  have hNz : ¬ zW ∈ fixV (S.plus K) := by
    intro hfix
    apply S.not_le_centralizer_z_of_inYz hK hT
    intro k hk
    have h1 := hfix _ (Setup.mem_autOn_iff.2 ⟨⟨k, hKW hk⟩, hk, rfl⟩)
    have h2 : k * S.z * k⁻¹ = S.z := by
      have := congrArg Subtype.val h1
      rwa [InternalSec.coe_conjAct_apply] at this
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k * S.z = k * S.z * k⁻¹ * k := by group
      _ = S.z * k := by rw [h2]
  have hvN : vW ∈ fixV (S.plus K) := by
    rw [mem_fixV]
    intro g hg
    obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := Setup.mem_autOn_iff.1 hg
    apply Subtype.ext
    rw [InternalSec.coe_conjAct_apply]
    have hkv := Subgroup.mem_centralizer_singleton_iff.mp (hK.1 hk)
    show k * S.v12 * k⁻¹ = S.v12
    rw [hkv, mul_inv_cancel_right]
  set φA : ↥(alternatingGroup (Fin 5)) →* MulAut ↥(S.WK K) :=
    φ.comp (alternatingGroup (Fin 5)).subtype with hφAdef
  have hφAi : Function.Injective φA := hφi.comp Subtype.val_injective
  have hφAr : φA.range = S.plus K := by
    ext n
    constructor
    · rintro ⟨σ, rfl⟩
      exact (hAm σ).mpr σ.2
    · intro hn
      obtain ⟨σ, rfl⟩ := hNφ hn
      exact ⟨⟨σ, (hAm σ).mp hn⟩, rfl⟩
  have hTvHK : IsSylowTwoOf (autOn S.Tv (S.WK K)) (autOn (S.HK K) (S.WK K)) :=
    Setup.isSylowTwoOf_autOn (S.isSylowTwoOf_Tv_HK h1222 h517 hK.1) hHKW
  have hNHK : S.plus K ≤ autOn (S.HK K) (S.WK K) := A4.autOn_mono hKHK
  have hQ : IsSylowTwoOf (autOn S.Tv (S.WK K) ⊓ S.plus K) (S.plus K) :=
    A4.isSylowTwoOf_inf_normal hTvHK hNHK hNH
  set D : Subgroup ↥(alternatingGroup (Fin 5)) := (autOn S.Tv (S.WK K) ⊓ S.plus K).comap φA
    with hDdef
  have hDmap : D.map φA = autOn S.Tv (S.WK K) ⊓ S.plus K :=
    Subgroup.map_comap_eq_self (hφAr ▸ inf_le_right)
  have hD : IsSylowTwoOf D ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have h2 : IsPGroup 2 ↥(D.map φA) := hDmap ▸ hQ.2.1
      exact h2.of_equiv (D.equivMapOfInjective φA hφAi).symm
    · have h3 := hQ.2.2
      show ¬ 2 ∣ D.relIndex ⊤
      rw [← Subgroup.relIndex_map_map_of_injective D ⊤ hφAi, hDmap, ← MonoidHom.range_eq_map,
        hφAr]
      exact h3
  have hx1 : Ψ zW ≠ 1 := fun h => hNz ((hker zW).mp h)
  have hxD : ∀ σ ∈ D, pact (σ : Equiv.Perm (Fin 5)) (Ψ zW) = Ψ zW := by
    intro σ hσ
    have hσT : φA σ ∈ autOn S.Tv (S.WK K) := hσ.1
    obtain ⟨⟨t, htN⟩, ht, hte⟩ := Setup.mem_autOn_iff.1 hσT
    have h1 : φA σ zW = zW := by
      rw [← hte]
      exact Subtype.ext (by
        rw [InternalSec.coe_conjAct_apply]
        exact S.conj_z_of_mem_T (Subgroup.mem_inf.mp ht).1)
    rw [← hΨe' (σ : Equiv.Perm (Fin 5)) zW]
    exact congrArg Ψ h1
  obtain ⟨p, hpx⟩ := exists_eq_wA_of_isSylowTwoOf hD hx1 hxD
  obtain ⟨l, hlLv, -, hlρ⟩ := S.exists_Lv_c234_odd
  have hyHK : (l : G) ∈ S.HK K := (le_sup_right.trans le_sup_left : S.Lv ≤ S.HK K) hlLv
  have hyW : (l : G) ∈ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hHKW hyHK
  set yp : MulAut ↥(S.WK K) := conjAct (S.WK K) ⟨(l : G), hyW⟩ with hypdef
  have hypN : yp ∈ Subgroup.normalizer (S.plus K : Set (MulAut ↥(S.WK K))) :=
    hNH (Setup.mem_autOn_iff.2 ⟨⟨(l : G), hyW⟩, hyHK, rfl⟩)
  have hypN' : yp⁻¹ ∈ Subgroup.normalizer (S.plus K : Set (MulAut ↥(S.WK K))) :=
    Subgroup.inv_mem _ hypN
  obtain ⟨s, hs⟩ := exists_perm_of_normalizes_quot Ψ hΨs (fun σ => φ σ) hΨe' yp
    (fun m hm => (hker _).mpr (mem_fixV_of_mem_normalizer hypN ((hker m).mp hm)))
    (fun m hm => (hker _).mpr (mem_fixV_of_mem_normalizer hypN' ((hker m).mp hm)))
    (fun σ hσ => by
      have h1 : yp * φ σ * yp⁻¹ ∈ S.plus K :=
        (Subgroup.mem_normalizer_iff.mp hypN _).mp ((hAm σ).mpr hσ)
      obtain ⟨τ, hτ⟩ := hNφ h1
      refine ⟨τ, (hAm τ).mp (hτ ▸ h1), fun m => ?_⟩
      show yp (φ σ m) = φ τ (yp m)
      rw [hτ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self])
    (fun τ hτ => by
      have h1 : yp⁻¹ * φ τ * yp⁻¹⁻¹ ∈ S.plus K :=
        (Subgroup.mem_normalizer_iff.mp hypN' _).mp ((hAm τ).mpr hτ)
      rw [inv_inv] at h1
      obtain ⟨σ, hσ⟩ := hNφ h1
      refine ⟨σ, (hAm σ).mp (hσ ▸ h1), fun m => ?_⟩
      show yp (φ σ m) = φ τ (yp m)
      rw [hσ, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self])
  have hprod : zW * yp zW * yp (yp zW) = vW := by
    have hlV := l.2
    set zV : ↥V := ⟨S.z, S.z_mem_V⟩ with hzVdef
    have hc1 : ((conjAct V l zV : ↥V) : G) = (l : G) * S.z * (l : G)⁻¹ :=
      InternalSec.coe_conjAct_apply l zV
    have hc2 : ((conjAct V l (conjAct V l zV) : ↥V) : G) =
        (l : G) * ((l : G) * S.z * (l : G)⁻¹) * (l : G)⁻¹ := by
      rw [InternalSec.coe_conjAct_apply, hc1]
    have hψ : S.frame.ψ (zV * conjAct V l zV * conjAct V l (conjAct V l zV)) =
        S.frame.ψ ⟨S.v12, S.v12_mem_V⟩ := by
      rw [map_mul, map_mul, S.frame.equiv, S.frame.equiv, S.frame.equiv, S.psi_z, S.psi_v12,
        ← MulAut.mul_apply, ← map_mul]
      rcases hlρ with h | h <;> rw [h]
      · rw [show c234 * c234 = c234⁻¹ by decide]
        exact W4_mul_pact_c234
      · rw [show c234⁻¹ * c234⁻¹ = c234 by decide]
        exact W4_mul_pact_c234_inv
    have hV := congrArg Subtype.val (S.frame.ψ.injective hψ)
    simp only [Subgroup.coe_mul] at hV
    rw [hc1, hc2] at hV
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hypdef, InternalSec.coe_conjAct_apply, InternalSec.coe_conjAct_apply,
      InternalSec.coe_conjAct_apply]
    exact hV
  have hΨprod : Ψ zW * pact s (Ψ zW) * pact s (pact s (Ψ zW)) = 1 := by
    calc Ψ zW * pact s (Ψ zW) * pact s (pact s (Ψ zW))
        = Ψ zW * Ψ (yp zW) * Ψ (yp (yp zW)) := by simp only [hs]
      _ = Ψ (zW * yp zW * yp (yp zW)) := by rw [map_mul, map_mul]
      _ = Ψ vW := by rw [hprod]
      _ = 1 := (hker vW).mpr hvN
  rw [hpx] at hΨprod
  exact mul_pact_wA_ne_one s p hΨprod

theorem nat_of_sl2_four
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) (h56 : AsB56)
    (hH : S.Hyp1367) {K : Subgroup G} [IsMulCommutative ↥(S.WK K)] (hK : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {F : Type} [Field F] [Finite F]
    (hF4 : Nat.card F = 4) (e : ↥(S.plus K) ≃* ↥(StSL 2 F)) :
    ∃ (G₂ : Subgroup (MulAut ↥(S.WK K))) (U C : Subgroup ↥(S.WK K)) (K' : Type) (_ : Field K')
      (_ : Finite K') (π : ↥(StSL 2 K') →* ↥(S.plus K)), Nat.card K' = 4 ∧
      S.plus K ⊔ G₂ = jStar (S.HK K) S.Tv (S.WK K) ∧ S.plus K ⊓ G₂ = ⊥ ∧
      (∀ a ∈ S.plus K, ∀ b ∈ G₂, a * b = b * a) ∧
      (FFModel.nat (StSL 2 K')).RealizesVia (S.plus K) U C π ∧
      (∀ g ∈ S.plus K, ∀ c ∈ C, g c = c) ∧
      (∀ g ∈ S.plus K, ∀ v : ↥(S.WK K), g v * v⁻¹ ∈ U) := by
  have hF' := hH.hF
  have hq := S.isQuasisimple_plus h1222 h517 hF' hK hT
  have hR := S.isTwoReducedIn_WK h1222 h517 hF' hK.1 hT
  have hWT := (S.WK_le_Tv h1222 h517 hF' hK.1 hT).1
  have hSQ := S.sqtkGroup_HK h1222 h517 hF' hK.1 hT
  have hKJ := S.plus_le_jStar h1222 h517 hF' hK hT
  have hJne : autOn (thompsonJ S.Tv) (S.WK K) ≠ ⊥ := by
    intro h
    have h1 := S.plus_eq_commutator h1222 h517 hF' hK hT
    rw [h, Subgroup.commutator_bot_right] at h1
    exact (qs_perfect_ne_bot hq).2 h1.symm
  have hcases := b56Cases_jStar h56 hWT (S.Tv_le_HK K) hR hSQ hJne
  have hb := b53Hyp_jStar hWT (S.Tv_le_HK K) hR hSQ
  have hNn : ∀ x ∈ jStar (S.HK K) S.Tv (S.WK K), ∀ m ∈ S.plus K, x * m * x⁻¹ ∈ S.plus K :=
    fun x hx m hm => (Subgroup.mem_normalizer_iff.mp
      (S.HK_le_normalizer_plus h1222 h517 hF' hK hT (jStar_le (S.Tv_le_HK K) hx)) m).mp hm
  have hV2 : ∀ v : ↥(S.WK K), v ^ 2 = 1 := fun v =>
    Subtype.ext (by rw [Subgroup.coe_pow, hR.2.2.1.2 _ v.2, Subgroup.coe_one])
  rcases sl2_four_of_b56 hV2 hb hcases hKJ hNn hq hF4 e with hnat |
    ⟨G₁, G₂, W₁, W₂, hNG₁, hsup, -, -, -, hW12, hWi, -, hinv₂, hW₁, hsym⟩
  · exact hnat
  · exact (S.false_of_symmetricNatural h1222 h517 hF' hK hT hF4 e hNG₁ (hsup ▸ le_sup_left) hW12
      hWi hinv₂ hW₁ hsym).elim

end Setting

end CFSG.Quasithin.H13.A5
