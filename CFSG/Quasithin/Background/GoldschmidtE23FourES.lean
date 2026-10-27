module

public import CFSG.Quasithin.Background.FixVLatticeSup
public import CFSG.Quasithin.Background.GoldschmidtE23FourFix
public import CFSG.Quasithin.Background.C126A5ExtractFam
public import CFSG.Quasithin.Background.C126Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

variable {G : Type} [Group G] [Finite G]

section Comm

variable {W : Type*} [CommGroup W]

theorem commV_mono' {X Y : Subgroup (MulAut W)} (h : X ≤ Y) : commV X ≤ commV Y :=
  Subgroup.closure_mono fun _ ⟨x, hx, v, hv⟩ => ⟨x, h hx, v, hv⟩

theorem commV_biSup_le' (I : Finset (Subgroup (MulAut W))) :
    commV (⨆ L ∈ I, L) ≤ ⨆ L ∈ I, commV L :=
  CFSG.Quasithin.FixVLat.commV_biSup_le I

theorem eq_one_of_mem_iSup_commV {I : Finset (Subgroup (MulAut W))}
    (hcard : I.card = 1 ∨ I.card = 2) {K : Subgroup (MulAut W)}
    (hinf : ∀ L ∈ I, commV L ⊓ (fixV K ⊔ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L') ≤ fixV K)
    (hL : ∀ L ∈ I, ∀ w ∈ commV L, w ∈ fixV K → w = 1) {w : W}
    (hw : w ∈ ⨆ L ∈ I, commV L) (hwK : w ∈ fixV K) : w = 1 := by
  classical
  rcases hcard with h | h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
    have : (⨆ L ∈ ({a} : Finset (Subgroup (MulAut W))), commV L) ≤ commV a :=
      iSup₂_le fun L hL => by rw [Finset.mem_singleton.1 hL]
    exact hL a (Finset.mem_singleton_self a) w (this hw) hwK
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 h
    have hsum : (⨆ L ∈ ({a, b} : Finset (Subgroup (MulAut W))), commV L) ≤
        commV a ⊔ commV b := iSup₂_le fun L hL => by
      rcases Finset.mem_insert.1 hL with rfl | hL
      · exact le_sup_left
      · rw [Finset.mem_singleton.1 hL]
        exact le_sup_right
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 (hsum hw)
    have hxK : x ∈ fixV K := by
      have hmem : x ∈ fixV K ⊔ ⨆ L' ∈ ({a, b} : Finset (Subgroup (MulAut W))),
          ⨆ (_ : L' ≠ a), commV L' := by
        have hle : commV b ≤ ⨆ L' ∈ ({a, b} : Finset (Subgroup (MulAut W))),
            ⨆ (_ : L' ≠ a), commV L' :=
          le_iSup₂_of_le (f := fun L' (_ : L' ∈ ({a, b} : Finset (Subgroup (MulAut W)))) =>
            ⨆ (_ : L' ≠ a), commV L') b (by simp) (le_iSup (fun _ : b ≠ a => commV b) hab.symm)
        have hyb := hle (inv_mem hy)
        have : x = (x * y) * y⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem_sup hwK hyb
      exact hinf a (by simp) ⟨hx, hmem⟩
    have hx1 : x = 1 := hL a (by simp) x hx hxK
    subst hx1
    have hyK : y ∈ fixV K := by simpa using hwK
    simpa using hL b (by simp) y hy hyK

end Comm

section Main

variable {H T M V : Subgroup G}

theorem not_le_centralizer_VZ_of_a5Case (hV : IsElemAbelian 2 V) (hmin : MinParabolic H T M)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hA5 : C126.A5Case H T V hV) : ¬ H ≤ Subgroup.centralizer (VZ T H : Set G) := by
  intro hES
  obtain ⟨hKJ, I, hfam, hall⟩ := hA5
  obtain ⟨hcard, hJeq, hcomm, hind, hconj, htype, hsup, hinf, h2, h3⟩ := hfam
  have hT := hmin.isSylow
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hTH : T ≤ H := hT.1
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTH.trans hHN
  have hKH : twoResidual H ≤ H := twoResidual_le H
  have hJH : thompsonJ H ≤ H := B6.thompsonJ_le H
  have hTt : IsPGroup 2 (autI hV T) := (B2F.isSylowTwoOf_autI hV hHN hT).2.1
  have hXJ : autI hV H ≤ Subgroup.normalizer
      (autI hV (thompsonJ H) : Set (MulAut (IntMod V hV))) :=
    C126.A5.autI_le_normalizer_autI hV (B6.le_normalizer_thompsonJ H)
  have hXK : autI hV H ≤ Subgroup.normalizer
      (autI hV (twoResidual H) : Set (MulAut (IntMod V hV))) :=
    C126.A5.autI_le_normalizer_autI hV (le_normalizer_twoResidual H)
  have hinv : ∀ t ∈ autI hV H, ∀ e ∈ commV (autI hV (thompsonJ H)),
      t e ∈ commV (autI hV (thompsonJ H)) := by
    intro t ht e he
    induction he using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y, hy, v, rfl⟩ := hx
      refine Subgroup.subset_closure ⟨t * y * t⁻¹, ?_, t v, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hXJ ht) y).mp hy
      · simp [MulAut.mul_apply]
    | one => simp
    | mul x y hx hy ihx ihy => simpa using (commV (autI hV (thompsonJ H))).mul_mem ihx ihy
    | inv x hx ih => simpa using (commV (autI hV (thompsonJ H))).inv_mem ih
  obtain ⟨L₀, hL₀⟩ : I.Nonempty := Finset.card_pos.1 (by rcases hcard with h | h <;> omega)
  have hL₀J : L₀ ≤ autI hV (thompsonJ H) :=
    hJeq ▸ le_iSup₂ (f := fun L (_ : L ∈ I) => L) L₀ hL₀
  obtain ⟨θ, β, hβ⟩ := hall L₀ hL₀
  have hx₀ : (![1, 1, 0, 0, 0] : Fin 5 → ZMod 2) ∈ evenWeight 5 := by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    decide
  let u₀ : ↥(commV L₀) := β.symm (Multiplicative.ofAdd ⟨_, hx₀⟩)
  have hu₀ : u₀ ≠ 1 := by
    intro h
    have h1 : β u₀ = 1 := by rw [h, map_one]
    have h2 : β u₀ = Multiplicative.ofAdd ⟨_, hx₀⟩ := by simp [u₀]
    rw [h2, ofAdd_eq_one] at h1
    have := congrArg (fun x : evenWeight 5 => (x : Fin 5 → ZMod 2) 0) h1
    simp at this
  have hne : (u₀ : IntMod V hV) ≠ 1 := fun h => hu₀ (Subtype.ext h)
  have he₀ : (u₀ : IntMod V hV) ∈ commV (autI hV (thompsonJ H)) := commV_mono' hL₀J u₀.2
  have h2dvd : 2 ∣ Nat.card (commV (autI hV (thompsonJ H))) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf (u₀ : IntMod V hV) = 2 := orderOf_eq_prime (IntMod.sq_eq_one _) hne
    have := orderOf_dvd_natCard (⟨(u₀ : IntMod V hV), he₀⟩ : commV (autI hV (thompsonJ H)))
    rwa [Subgroup.orderOf_mk, hord] at this
  obtain ⟨w, hwE, hw1, hwT⟩ := exists_fixed_of_isPGroup (MonoidHom.id (MulAut (IntMod V hV))) hTt
    (commV (autI hV (thompsonJ H))) (fun t ht e he => hinv t (autI_mono hV hTH ht) e he) h2dvd
  have hwTfix : w ∈ fixV (autI hV T) := fun t ht => hwT t ht
  have hwC : w.val ∈ Subgroup.centralizer (T : Set G) := (mem_fixV_autI hV hTN w).1 hwTfix
  have hVT : V ≤ T :=
    (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hw2 : w.val ^ 2 = 1 := by
    have := congrArg IntMod.val (IntMod.sq_eq_one w)
    simpa [pow_two] using this
  have hwZ : w.val ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨hVT w.val_mem, hwC⟩, hw2⟩
  have hwV : w.val ∈ VZ T H := le_conjClosure _ _ hwZ
  have hwCH : w.val ∈ Subgroup.centralizer (H : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun h hh =>
      (Subgroup.mem_centralizer_iff.1 (hES hh) w.val hwV).symm
  have hwX : w ∈ fixV (autI hV H) := (mem_fixV_autI hV hHN w).2 hwCH
  have hwK : w ∈ fixV (autI hV (twoResidual H)) := B1.fixV_le_fixV (autI_mono hV hKH) hwX
  have hJsup : thompsonJ H = twoResidual H ⊔ thompsonJ T := by
    refine MinParabolic.thompsonJ_eq_sup hmin hred ?_
    intro hbot
    apply hJ
    rwa [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
  have hsupJ : autI hV (thompsonJ T) ⊔ autI hV (twoResidual H) = autI hV (thompsonJ H) := by
    rw [hJsup, autI_sup hV (hKH.trans hHN) ((B6.thompsonJ_le T).trans (hTH.trans hHN)), sup_comm]
  have hP2 : IsPGroup 2 (autI hV (thompsonJ T)) := hTt.to_le (autI_mono hV (B6.thompsonJ_le T))
  have hD : ∀ y ∈ autI hV (thompsonJ H), ∃ k : ℕ, y ^ 2 ^ k ∈ autI hV (twoResidual H) :=
    B6.isTwoQuotient_of_sup_eq hP2 (fun y hy => hXK (autI_mono hV hJH hy)) hsupJ
  have hL : ∀ L ∈ I, ∀ w ∈ commV L, w ∈ fixV (autI hV (twoResidual H)) → w = 1 := by
    intro L hL w hw hwK
    obtain ⟨h₁, hh₁, h₂, hh₂, h13, h23, hfix⟩ := exists_threeCycles_of_isA5Module (hall L hL)
    have hLJ : L ≤ autI hV (thompsonJ H) := hJeq ▸ le_iSup₂ (f := fun L (_ : L ∈ I) => L) L hL
    exact hfix w hw (hwK h₁ (mem_of_pow_three_eq_one hD (hLJ hh₁) h13))
      (hwK h₂ (mem_of_pow_three_eq_one hD (hLJ hh₂) h23))
  have hwJ : w ∈ ⨆ L ∈ I, commV L := by
    have : commV (autI hV (thompsonJ H)) ≤ ⨆ L ∈ I, commV L := by
      rw [hJeq]
      exact commV_biSup_le' I
    exact this hwE
  exact hw1 (eq_one_of_mem_iSup_commV hcard hinf hL hwJ hwK)

end Main

end E2

end CFSG.Quasithin
