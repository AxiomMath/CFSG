module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Milestones.ASVolI.I2
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.CGT.Timmesfeld75.Statements
import CFSG.RankThree.PartTwo.Late.GammaZero
import CFSG.RankThree.PartTwo.Sec13.Statements
import CFSG.RankThree.PartTwo.Sec18.Notation
import CFSG.RankThree.PartTwo.Sec18.Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem Subgroup
open CFSG.ASVolI.ChIJK (IsSplitBNPair)
open scoped Pointwise

section Unit

variable {X : Type*} [Group X]

structure uc22p20jSplitUnit (p : ℕ) (B N U : Subgroup X) : Prop where
  hUB : U ≤ B
  hBU : ∀ b ∈ B, ∃ h ∈ B ⊓ N, ∃ u ∈ U, b = h * u
  hUn : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U
  hpel : ∀ b ∈ B, (∃ k : ℕ, b ^ (p ^ k) = 1) → b ∈ U
  hNU : ∀ g : X, (∀ u ∈ U, g * u * g⁻¹ ∈ U) → g ∈ B
  hUp : IsPGroup p U

variable {B N U : Subgroup X} [(cartan B N).Normal] {p : ℕ}

theorem uc22p20jSplitUnit.exists_unit_mul (hS : uc22p20jSplitUnit p B N U) {b : X} (hb : b ∈ B) :
    ∃ u ∈ U, ∃ h ∈ B ⊓ N, b = u * h := by
  obtain ⟨h, hh, u, hu, he⟩ := hS.hBU b⁻¹ (B.inv_mem hb)
  refine ⟨u⁻¹, U.inv_mem hu, h⁻¹, (B ⊓ N).inv_mem hh, ?_⟩
  have : b = (b⁻¹)⁻¹ := (inv_inv b).symm
  rw [this, he]
  simp [mul_inv_rev]

theorem uc22p20jSplitUnit.exists_monomial (hS : uc22p20jSplitUnit p B N U) {Y : Subgroup X} (hUY : U ≤ Y)
    {w : WeylGroup B N} {y : X} (hy : y ∈ Y) (hyw : y ∈ dc B N w) :
    ∃ n : N, (n : WeylGroup B N) = w ∧ (n : X) ∈ Y := by
  obtain ⟨n, hn, b, hb, b', hb', rfl⟩ := mem_dc_iff.1 hyw
  obtain ⟨u₁, hu₁, h₁, hh₁, rfl⟩ := hS.exists_unit_mul hb
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := hS.hBU b' hb'
  have hN₁ : h₁ ∈ N := (Subgroup.mem_inf.1 hh₁).2
  have hN₂ : h₂ ∈ N := (Subgroup.mem_inf.1 hh₂).2
  refine ⟨⟨h₁, hN₁⟩ * n * ⟨h₂, hN₂⟩, ?_, ?_⟩
  ·
    rw [← hn]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    have e1 : ((⟨h₁, hN₁⟩ : N) : WeylGroup B N) = 1 := by
      rw [mk_eq_one_iff]; exact (Subgroup.mem_inf.1 hh₁).1
    have e2 : ((⟨h₂, hN₂⟩ : N) : WeylGroup B N) = 1 := by
      rw [mk_eq_one_iff]; exact (Subgroup.mem_inf.1 hh₂).1
    rw [e1, e2]; simp
  · have e : ((⟨h₁, hN₁⟩ * n * ⟨h₂, hN₂⟩ : N) : X) = (u₁)⁻¹ * (u₁ * h₁ * (n : X) * (h₂ * u₂)) * u₂⁻¹ := by
      simp [mul_assoc]
    rw [e]
    exact Y.mul_mem (Y.mul_mem (Y.inv_mem (hUY hu₁)) hy) (Y.inv_mem (hUY hu₂))

variable {S : Set (WeylGroup B N)}

theorem uc22p20j_pel_conj {g u : X} {p k : ℕ} (h : u ^ (p ^ k) = 1) : (g⁻¹ * u * g) ^ (p ^ k) = 1 := by
  rw [show g⁻¹ * u * g = (MulAut.conj g⁻¹) u by simp [MulAut.conj_apply], ← map_pow, h, map_one]

theorem uc22p20jSplitUnit.exists_unit_conj_not_mem (hbn : IsBNPair B N S)
    (hS : uc22p20jSplitUnit p B N U) {s : WeylGroup B N} (hs : s ∈ S) {sn : N}
    (hsn : (sn : WeylGroup B N) = s) : ∃ u ∈ U, (sn : X)⁻¹ * u * (sn : X) ∉ B := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ u ∈ U, ((sn : X)⁻¹) * u * ((sn : X)⁻¹)⁻¹ ∈ U := by
    intro u hu
    have hB : (sn : X)⁻¹ * u * (sn : X) ∈ B := hcon u hu
    refine hS.hpel _ (by simpa using hB) ?_
    obtain ⟨k, hk⟩ := hS.hUp ⟨u, hu⟩
    refine ⟨k, ?_⟩
    have hk' : u ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    simpa using uc22p20j_pel_conj (g := (sn : X)) hk'
  have hsB : ((sn : X)⁻¹) ∈ B := hS.hNU _ hmem
  have hsB' : (sn : X) ∈ B := by simpa using B.inv_mem hsB
  have : (sn : WeylGroup B N) = 1 := mk_eq_one_iff.2 hsB'
  rw [hsn] at this
  exact hbn.ne_one hs this

theorem uc22p20jSplitUnit.exists_mem_dc_of_descent (hbn : IsBNPair B N S) (hS : uc22p20jSplitUnit p B N U)
    {Y : Subgroup X} {n : N} (hnU : ∀ u ∈ U, (n : X) * u * (n : X)⁻¹ ∈ Y) {s : WeylGroup B N}
    (hs : s ∈ S)
    (hdesc : wordLength S (s * (n : WeylGroup B N)) < wordLength S (n : WeylGroup B N)) :
    ∃ v ∈ Y, v ∈ dc B N s := by
  classical
  have hss : s * s = 1 := hbn.mul_self_eq_one hs
  obtain ⟨sn, hsn⟩ := QuotientGroup.mk_surjective s
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hex : ∃ u ∈ U, (sn : X)⁻¹ * u * (sn : X) ∉ B := hS.exists_unit_conj_not_mem hbn hs hsn
  obtain ⟨u, huU, hunB⟩ := hex
  have hsP : (sn : X) ∈ dc B N s := hsn ▸ coe_mem_dc sn
  have hsS : ({s} : Set (WeylGroup B N)) ⊆ S := Set.singleton_subset_iff.2 hs
  have hPs_ge : B ≤ parabolic B N {s} := hbn.le_parabolic hsS
  have hsnP : (sn : X) ∈ parabolic B N {s} :=
    hbn.dc_subset_parabolic hsS (Subgroup.subset_closure rfl) hsP
  set t : X := (sn : X)⁻¹ * u * (sn : X) with ht
  have htP : t ∈ parabolic B N {s} :=
    mul_mem (mul_mem (inv_mem hsnP) (hPs_ge (hS.hUB huU))) hsnP
  obtain ⟨w₀, hw₀, htw⟩ := (hbn.mem_parabolic_iff hsS).1 htP
  have htdc : t ∈ dc B N s := by
    rcases eq_one_or_eq_of_mem_closure_singleton hss hw₀ with rfl | rfl
    · exact absurd ((mem_dc_one).1 htw) hunB
    · exact htw
  set w : WeylGroup B N := (n : WeylGroup B N) with hw
  set n' : N := (sn)⁻¹ * n with hn'
  have hn'w : (n' : WeylGroup B N) = s * w := by
    rw [hn', QuotientGroup.mk_mul, QuotientGroup.mk_inv, hsn, hsinv]
  have hlen : wordLength S (n' : WeylGroup B N) < wordLength S (s * (n' : WeylGroup B N)) := by
    rw [hn'w]
    have : s * (s * w) = w := by rw [← mul_assoc, hss, one_mul]
    rw [this]; exact hdesc
  have hprod := hbn.bnCore.mul_subset_of_lt hs (hbn.mem_closure _) hlen
  have h1 : t⁻¹ * (n' : X) ∈ dc B N (s * (n' : WeylGroup B N)) := by
    apply hprod
    refine Set.mem_mul.2 ⟨t⁻¹, ?_, (n' : X), coe_mem_dc n', rfl⟩
    have := inv_mem_dc htdc
    rwa [hsinv] at this
  have h2 : ((n' : X)⁻¹) * t ∈ dc B N (w⁻¹) := by
    have h5 := inv_mem_dc h1
    have e : (s * (n' : WeylGroup B N))⁻¹ = w⁻¹ := by
      rw [hn'w, ← mul_assoc, hss, one_mul]
    rw [e] at h5
    simpa [mul_inv_rev] using h5
  have h3 : (n : X)⁻¹ * (u * (sn : X)) ∈ dc B N (w⁻¹) := by
    have e : (n : X)⁻¹ * (u * (sn : X)) = ((n' : X)⁻¹) * t := by
      simp [hn', ht, mul_assoc]
    rwa [e]
  have hnW : ((n⁻¹ : N) : WeylGroup B N) = w⁻¹ := by rw [hw, QuotientGroup.mk_inv]
  obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := (mem_dc_of_lift hnW).1 h3
  obtain ⟨h, hh, u'', hu'', hb₁e⟩ := hS.hBU b₁ hb₁
  have hhN : h ∈ N := (Subgroup.mem_inf.1 hh).2
  set hN : N := ⟨h, hhN⟩ with hhNdef
  have hconj : n * hN * n⁻¹ ∈ cartan B N := by
    refine (inferInstance : (cartan B N).Normal).conj_mem hN ?_ n
    exact Subgroup.mem_subgroupOf.2 hh
  have hconjB : ((n * hN * n⁻¹ : N) : X) ∈ B := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hconj)).1
  refine ⟨(n : X) * u'' * (n : X)⁻¹, ?_, ?_⟩
  · exact hnU u'' hu''
  · have hsu : u * (sn : X) ∈ dc B N s := by
      simpa using mul_mem_dc hsP (hS.hUB huU) B.one_mem
    refine mem_dc_of_mem hsu (b := (((n * hN * n⁻¹ : N) : X))⁻¹) (b' := b₂⁻¹)
      (B.inv_mem hconjB) (B.inv_mem hb₂) ?_
    have hb' : (n : X)⁻¹ * (u * (sn : X)) = b₁ * (n : X)⁻¹ * b₂ := by simpa using hb
    have hu_eq : u * (sn : X) = (n : X) * b₁ * (n : X)⁻¹ * b₂ := by
      have := congrArg (fun z => (n : X) * z) hb'
      simp only [← mul_assoc, mul_inv_cancel, one_mul] at this
      simpa [mul_assoc] using this
    have hcoe : ((n * hN * n⁻¹ : N) : X) = (n : X) * h * (n : X)⁻¹ := by
      simp [hhNdef]
    rw [hu_eq, hb₁e, hcoe]
    group

@[expose] def uc22p20jJset (S : Set (WeylGroup B N)) (Y : Subgroup X) : Set (WeylGroup B N) :=
  {s | s ∈ S ∧ ∃ y ∈ Y, y ∈ dc B N s}

theorem uc22p20jSplitUnit.monomial_mem_closure (hbn : IsBNPair B N S) (hS : uc22p20jSplitUnit p B N U)
    {Y : Subgroup X} (hUY : U ≤ Y) :
    ∀ (k : ℕ) (n : N), wordLength S (n : WeylGroup B N) = k → (n : X) ∈ Y →
      (n : WeylGroup B N) ∈ Subgroup.closure (uc22p20jJset S Y) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk hn
    by_cases hw1 : (n : WeylGroup B N) = 1
    · rw [hw1]; exact Subgroup.one_mem _
    obtain ⟨s, hs, hdesc⟩ := exists_left_descent (fun s hs => hbn.mul_self_eq_one hs)
      (hbn.mem_closure _) hw1
    have hlt : wordLength S (s * (n : WeylGroup B N)) < wordLength S (n : WeylGroup B N) := by omega
    have hnU : ∀ u ∈ U, (n : X) * u * (n : X)⁻¹ ∈ Y := fun u hu =>
      Y.mul_mem (Y.mul_mem hn (hUY hu)) (Y.inv_mem hn)
    obtain ⟨v, hvY, hvdc⟩ := hS.exists_mem_dc_of_descent hbn hnU hs hlt
    obtain ⟨m, hm, hmY⟩ := hS.exists_monomial hUY hvY hvdc
    have hsJ : s ∈ uc22p20jJset S Y := ⟨hs, v, hvY, hvdc⟩
    have hss : s * s = 1 := hbn.mul_self_eq_one hs
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hn₂Y : ((m⁻¹ * n : N) : X) ∈ Y := by
      simpa using Y.mul_mem (Y.inv_mem hmY) hn
    have hn₂W : ((m⁻¹ * n : N) : WeylGroup B N) = s * (n : WeylGroup B N) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hm, hsinv]
    have := ih (wordLength S (s * (n : WeylGroup B N))) (by omega) (m⁻¹ * n) (by rw [hn₂W]) hn₂Y
    rw [hn₂W] at this
    have e : (n : WeylGroup B N) = s * (s * (n : WeylGroup B N)) := by
      rw [← mul_assoc, hss, one_mul]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure hsJ) this

theorem uc22p20jSplitUnit.le_parabolic_Jset (hbn : IsBNPair B N S) (hS : uc22p20jSplitUnit p B N U)
    {Y : Subgroup X} (hUY : U ≤ Y) : Y ≤ parabolic B N (uc22p20jJset S Y) := by
  intro y hy
  have hJS : uc22p20jJset S Y ⊆ S := fun s hs => hs.1
  obtain ⟨w, hw⟩ := hbn.exists_mem_dc y
  obtain ⟨n, hnw, hnY⟩ := hS.exists_monomial hUY hy hw
  have := hS.monomial_mem_closure hbn hUY _ n rfl hnY
  rw [hnw] at this
  exact (hbn.mem_parabolic_iff_of_mem_dc hJS hw).2 this

theorem uc22p20jSplitUnit.dc_form (hS : uc22p20jSplitUnit p B N U) {w : WeylGroup B N} {n : N}
    (hn : (n : WeylGroup B N) = w) {x : X} (hx : x ∈ dc B N w) :
    ∃ u ∈ U, ∃ b ∈ B, x = u * (n : X) * b := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_dc_of_lift hn).1 hx
  obtain ⟨u, hu, h, hh, rfl⟩ := hS.exists_unit_mul hb₁
  have hhN : h ∈ N := (Subgroup.mem_inf.1 hh).2
  have hconj : n⁻¹ * (⟨h, hhN⟩ : N) * n ∈ cartan B N := by
    have := (inferInstance : (cartan B N).Normal).conj_mem (⟨h, hhN⟩ : N)
      (Subgroup.mem_subgroupOf.2 hh) n⁻¹
    simpa using this
  have hconjB : (n : X)⁻¹ * h * (n : X) ∈ B := by
    have := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hconj)).1
    simpa using this
  refine ⟨u, hu, (n : X)⁻¹ * h * (n : X) * b₂, B.mul_mem hconjB hb₂, ?_⟩
  group

theorem uc22p20jSplitUnit.conj_le_of_mem_Jset (hbn : IsBNPair B N S) (hS : uc22p20jSplitUnit p B N U)
    {Y : Subgroup X} (hUY : U ≤ Y) {s : WeylGroup B N} (hs : s ∈ uc22p20jJset S Y) {g : X}
    (hg : g ∈ parabolic B N {s}) : ∀ u ∈ U, g * u * g⁻¹ ∈ Y := by
  intro u hu
  have hss : s * s = 1 := hbn.mul_self_eq_one hs.1
  have hsS : ({s} : Set (WeylGroup B N)) ⊆ S := Set.singleton_subset_iff.2 hs.1
  obtain ⟨w₀, hw₀, hgw⟩ := (hbn.mem_parabolic_iff hsS).1 hg
  rcases eq_one_or_eq_of_mem_closure_singleton hss hw₀ with rfl | rfl
  · exact hUY (hS.hUn g ((mem_dc_one).1 hgw) u hu)
  · obtain ⟨sn, hsn⟩ := QuotientGroup.mk_surjective w₀
    obtain ⟨v, hvY, hvdc⟩ := hs.2
    obtain ⟨u₂, hu₂, b₂, hb₂, hge⟩ := hS.dc_form hsn hgw
    obtain ⟨u₁, hu₁, b₁, hb₁, hve⟩ := hS.dc_form hsn hvdc
    have hy : u₂ * u₁⁻¹ * v ∈ Y := Y.mul_mem (Y.mul_mem (hUY hu₂) (Y.inv_mem (hUY hu₁))) hvY
    have hc : b₁⁻¹ * b₂ ∈ B := B.mul_mem (B.inv_mem hb₁) hb₂
    have hgy : g = (u₂ * u₁⁻¹ * v) * (b₁⁻¹ * b₂) := by
      rw [hge, hve]; group
    have hcu : (b₁⁻¹ * b₂) * u * (b₁⁻¹ * b₂)⁻¹ ∈ U := hS.hUn _ hc u hu
    have : g * u * g⁻¹ = (u₂ * u₁⁻¹ * v) * ((b₁⁻¹ * b₂) * u * (b₁⁻¹ * b₂)⁻¹) * (u₂ * u₁⁻¹ * v)⁻¹ := by
      rw [hgy]; group
    rw [this]
    exact Y.mul_mem (Y.mul_mem hy (hUY hcu)) (Y.inv_mem hy)

@[expose] def uc22p20jN2J (B N U : Subgroup X) [(cartan B N).Normal] (J : Set (WeylGroup B N)) : Subgroup X :=
  Subgroup.closure {x | ∃ s ∈ J, ∃ g ∈ parabolic B N {s}, ∃ u ∈ U, x = g * u * g⁻¹}

theorem uc22p20jSplitUnit.N2J_le (hbn : IsBNPair B N S) (hS : uc22p20jSplitUnit p B N U) {Y : Subgroup X}
    (hUY : U ≤ Y) : uc22p20jN2J B N U (uc22p20jJset S Y) ≤ Y := by
  refine (Subgroup.closure_le Y).2 ?_
  rintro x ⟨s, hs, g, hg, u, hu, rfl⟩
  exact hS.conj_le_of_mem_Jset hbn hUY hs hg u hu

theorem uc22p20j_mem_sup_of_le_normalizer {N K : Subgroup X} (hK : K ≤ normalizer (N : Set X)) {x : X}
    (hx : x ∈ N ⊔ K) : ∃ n ∈ N, ∃ k ∈ K, x = n * k := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, K.one_mem, by simp⟩
    · exact ⟨1, N.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, N.one_mem, 1, K.one_mem, by simp⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨n₁, hn₁, k₁, hk₁, rfl⟩ := iha
    obtain ⟨n₂, hn₂, k₂, hk₂, rfl⟩ := ihb
    refine ⟨n₁ * (k₁ * n₂ * k₁⁻¹), N.mul_mem hn₁ ?_, k₁ * k₂, K.mul_mem hk₁ hk₂, by group⟩
    exact (Subgroup.mem_normalizer_iff.1 (hK hk₁) n₂).1 hn₂
  | inv a _ ih =>
    obtain ⟨n, hn, k, hk, rfl⟩ := ih
    refine ⟨k⁻¹ * n⁻¹ * k⁻¹⁻¹, ?_, k⁻¹, K.inv_mem hk, by group⟩
    exact (Subgroup.mem_normalizer_iff.1 (hK (K.inv_mem hk)) n⁻¹).1 (N.inv_mem hn)

theorem uc22p20j_N2J_conj (hS : uc22p20jSplitUnit p B N U) {J : Set (WeylGroup B N)} {b : X} (hb : b ∈ B) :
    ∀ x ∈ uc22p20jN2J B N U J, b * x * b⁻¹ ∈ uc22p20jN2J B N U J := by
  have hBP : ∀ s : WeylGroup B N, b ∈ parabolic B N {s} := fun s =>
    Subgroup.subset_closure (le_parabolic_one _ hb)
  intro x hx
  have : uc22p20jN2J B N U J ≤ (uc22p20jN2J B N U J).comap (MulAut.conj b).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨s, hs, g, hg, u, hu, rfl⟩
    refine Subgroup.subset_closure ⟨s, hs, b * g, Subgroup.mul_mem _ (hBP s) hg, u, hu, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  simpa [MulAut.conj_apply] using this hx

theorem uc22p20jSplitUnit.U_le_N2J (hS : uc22p20jSplitUnit p B N U) {J : Set (WeylGroup B N)} (hJ : J.Nonempty) :
    U ≤ uc22p20jN2J B N U J := by
  intro u hu
  obtain ⟨s, hs⟩ := hJ
  exact Subgroup.subset_closure ⟨s, hs, 1, Subgroup.one_mem _, u, hu, by simp⟩

theorem uc22p20jSplitUnit.dc_le_N2J_sup (hbn : IsBNPair B N S) (hS : uc22p20jSplitUnit p B N U)
    {J : Set (WeylGroup B N)} (hJS : J ⊆ S) {s : WeylGroup B N} (hs : s ∈ J) :
    ∀ x ∈ dc B N s, x ∈ uc22p20jN2J B N U J ⊔ B := by
  intro x hx
  have hss : s * s = 1 := hbn.mul_self_eq_one (hJS hs)
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective s
  have hsS : ({s} : Set (WeylGroup B N)) ⊆ S := Set.singleton_subset_iff.2 (hJS hs)
  have hmP : (m : X) ∈ parabolic B N {s} :=
    hbn.dc_subset_parabolic hsS (Subgroup.subset_closure rfl) (hm ▸ coe_mem_dc m)
  have hnU : ∀ u ∈ U, (m : X) * u * (m : X)⁻¹ ∈ uc22p20jN2J B N U J := fun u hu =>
    Subgroup.subset_closure ⟨s, hs, m, hmP, u, hu, rfl⟩
  have hdesc : wordLength S (s * (m : WeylGroup B N)) < wordLength S (m : WeylGroup B N) := by
    rw [hm, hss]
    have h0 : wordLength S (1 : WeylGroup B N) = 0 := wordLength_one
    have hpos : wordLength S s ≠ 0 := by
      intro h
      exact hbn.ne_one (hJS hs) ((wordLength_eq_zero_iff (fun s hs => hbn.mul_self_eq_one hs)
        (hbn.mem_closure s)).1 h)
    omega
  obtain ⟨v, hvN, hvdc⟩ := hS.exists_mem_dc_of_descent hbn hnU (hJS hs) hdesc
  obtain ⟨u₁, hu₁, b₁, hb₁, hve⟩ := hS.dc_form hm hvdc
  obtain ⟨u₂, hu₂, b₂, hb₂, hxe⟩ := hS.dc_form hm hx
  have hUN := hS.U_le_N2J ⟨s, hs⟩
  have : x = (u₂ * u₁⁻¹) * v * (b₁⁻¹ * b₂) := by rw [hxe, hve]; group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left
    (Subgroup.mul_mem _ (hUN hu₂) (Subgroup.inv_mem _ (hUN hu₁)))) (Subgroup.mem_sup_left hvN))
    (Subgroup.mem_sup_right (B.mul_mem (B.inv_mem hb₁) hb₂))

theorem uc22p20jSplitUnit.parabolic_le_sup (hbn : IsBNPair B N S) (hS : uc22p20jSplitUnit p B N U)
    {J : Set (WeylGroup B N)} (hJS : J ⊆ S) : parabolic B N J ≤ uc22p20jN2J B N U J ⊔ B := by
  set K := uc22p20jN2J B N U J ⊔ B with hK
  have hdc : ∀ w ∈ Subgroup.closure J, ∀ x ∈ dc B N w, x ∈ K := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem s hs => intro x hx; exact hS.dc_le_N2J_sup hbn hJS hs x hx
    | one => intro x hx; exact Subgroup.mem_sup_right ((mem_dc_one).1 hx)
    | mul a b _ _ iha ihb =>
      intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 (dc_mul_subset_of a b hx)
      exact K.mul_mem (iha y hy) (ihb z hz)
    | inv a _ iha =>
      intro x hx
      have h1 : x⁻¹ ∈ dc B N a := by simpa using inv_mem_dc hx
      simpa using K.inv_mem (iha _ h1)
  refine (Subgroup.closure_le K).2 ?_
  intro x hx
  obtain ⟨w, hw, hxw⟩ := mem_parabolicSet_iff.1 hx
  exact hdc w hw x hxw

open CFSG.RankThree.PartTwo.Sec18 in
theorem uc22p20j_sandwich_abstract [Finite X] (hbn : IsBNPair B N S) (hS : uc22p20jSplitUnit p B N U)
    (hBsolv : Group.IsSolvable B) {Y : Subgroup X} (hUY : U ≤ Y) :
    ∃ P : Subgroup X, B ≤ P ∧ Y ≤ P ∧ CFSG.inSubgroup CFSG.perfectResidual P ≤ Y := by
  have hJS : uc22p20jJset S Y ⊆ S := fun s hs => hs.1
  set J := uc22p20jJset S Y with hJ
  set P := parabolic B N J with hP
  have hBP : B ≤ P := hbn.le_parabolic hJS
  refine ⟨P, hBP, hS.le_parabolic_Jset hbn hUY, ?_⟩
  set N₂ := uc22p20jN2J B N U J with hN₂
  have hN₂Y : N₂ ≤ Y := hS.N2J_le hbn hUY
  have hNP : N₂ ≤ P := by
    refine (Subgroup.closure_le P).2 ?_
    rintro x ⟨s, hs, g, hg, u, hu, rfl⟩
    have hsS : ({s} : Set (WeylGroup B N)) ⊆ S := Set.singleton_subset_iff.2 (hJS hs)
    have hgP : g ∈ P := (hbn.parabolic_le_iff hsS hJS).2 (Set.singleton_subset_iff.2 hs) hg
    exact P.mul_mem (P.mul_mem hgP (hBP (hS.hUB hu))) (P.inv_mem hgP)
  have hPle : P ≤ N₂ ⊔ B := hS.parabolic_le_sup hbn hJS
  have hBnorm : B ≤ normalizer (N₂ : Set X) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨uc22p20j_N2J_conj hS hb x, fun hx => ?_⟩
    have := uc22p20j_N2J_conj hS (B.inv_mem hb) _ hx
    simpa [mul_assoc] using this
  have hPnorm : P ≤ normalizer (N₂ : Set X) := hPle.trans (sup_le Subgroup.le_normalizer hBnorm)
  haveI : (N₂.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).2 hPnorm
  have hsolv : Group.IsSolvable (P ⧸ N₂.subgroupOf P) := by
    let ψ : B →* P ⧸ N₂.subgroupOf P := (QuotientGroup.mk' (N₂.subgroupOf P)).comp (Subgroup.inclusion hBP)
    have hψ : Function.Surjective ψ := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨n, hn, k, hk, hxe⟩ := uc22p20j_mem_sup_of_le_normalizer hBnorm (hPle x.2)
      refine ⟨⟨k, hk⟩, ?_⟩
      show QuotientGroup.mk (Subgroup.inclusion hBP ⟨k, hk⟩) = QuotientGroup.mk x
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hxe' : (x : X) = n * k := hxe
      have : (((Subgroup.inclusion hBP ⟨k, hk⟩)⁻¹ * x : P) : X) = k⁻¹ * n * k := by
        simp [hxe', mul_assoc]
      rw [this]
      have := uc22p20j_N2J_conj hS (B.inv_mem hk) n hn
      simpa [mul_assoc] using this
    haveI := hBsolv
    exact solvable_of_surjective hψ
  exact (inSubgroup_perfectResidual_le_of_isSolvable hNP hsolv).trans hN₂Y

theorem uc22p20j_parabolic_empty_le : parabolic B N (∅ : Set (WeylGroup B N)) ≤ B := by
  refine (Subgroup.closure_le B).2 ?_
  intro x hx
  obtain ⟨w, hw, hxw⟩ := mem_parabolicSet_iff.1 hx
  rw [Subgroup.closure_empty, Subgroup.mem_bot] at hw
  subst hw
  exact (mem_dc_one).1 hxw

theorem uc22p20jSplitUnit.N2J_le_parabolic (hbn : IsBNPair B N S) (hS : uc22p20jSplitUnit p B N U)
    {J : Set (WeylGroup B N)} (hJS : J ⊆ S) : uc22p20jN2J B N U J ≤ parabolic B N J := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨s, hs, g, hg, u, hu, rfl⟩
  have hsS : ({s} : Set (WeylGroup B N)) ⊆ S := Set.singleton_subset_iff.2 (hJS hs)
  have hgP : g ∈ parabolic B N J := (hbn.parabolic_le_iff hsS hJS).2 (Set.singleton_subset_iff.2 hs) hg
  have hBP : B ≤ parabolic B N J := hbn.le_parabolic hJS
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgP (hBP (hS.hUB hu))) (Subgroup.inv_mem _ hgP)

theorem uc22p20jSplitUnit.B_le_normalizer_N2J (hS : uc22p20jSplitUnit p B N U) (J : Set (WeylGroup B N)) :
    B ≤ normalizer (uc22p20jN2J B N U J : Set X) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨uc22p20j_N2J_conj hS hb x, fun hx => ?_⟩
  have := uc22p20j_N2J_conj hS (B.inv_mem hb) _ hx
  simpa [mul_assoc] using this

theorem uc22p20jSplitUnit.N2J_single_le (hbn : IsBNPair B N S) (hS : uc22p20jSplitUnit p B N U) {Y : Subgroup X}
    (hUY : U ≤ Y) {s : WeylGroup B N} (hs : s ∈ uc22p20jJset S Y) : uc22p20jN2J B N U {s} ≤ Y := by
  refine (Subgroup.closure_le Y).2 ?_
  rintro x ⟨s', hs', g, hg, u, hu, rfl⟩
  have hss : s' = s := hs'
  subst hss
  exact hS.conj_le_of_mem_Jset hbn hUY hs hg u hu

theorem uc22p20j_mem_normalizer_of_conj_le [Finite X] {H : Subgroup X} {g : X}
    (h : ∀ u ∈ H, g * u * g⁻¹ ∈ H) : g ∈ normalizer (H : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  have hinj : Function.Injective (fun u : H => (⟨g * u * g⁻¹, h u u.2⟩ : H)) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simpa using this
  obtain ⟨u, hu⟩ := Finite.surjective_of_injective hinj ⟨g * x * g⁻¹, hx⟩
  have : g * (u : X) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hu
  have hux : (u : X) = x := by simpa using this
  rw [← hux]; exact u.2
end Unit

section Transport

variable {Z : Type} [Group Z] [Finite Z]

theorem uc22p20j_exists_splitUnit {B N : Subgroup Z} [(cartan B N).Normal]
    (hBN : CFSG.ASVolI.ChIJK.IsSplitBNPair 2 B N) :
    ∃ U : Sylow 2 Z, normalizer ((U : Subgroup Z) : Set Z) = B ∧
      uc22p20jSplitUnit 2 B N (U : Subgroup Z) ∧ Group.IsSolvable B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U₀, hUB, hUn, hUp, hUi, hUN, hUH, hsat⟩ := hBN.split
  obtain ⟨U, hUnorm⟩ := CFSG.ASVolI.ChIJK.IsSplitBNPair.exists_sylow_normalizer Nat.prime_two hBN
  let Us : Sylow 2 Z := hUp.toSylow hUi
  have hnormB : ∀ b ∈ B, ∀ u ∈ U₀, b * u * b⁻¹ ∈ U₀ := fun b hb u hu =>
    (Subgroup.normal_subgroupOf_iff hUB).1 hUn u b hu hb
  have hBnorm : B ≤ normalizer (U₀ : Set Z) := (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).1 hUn
  have hdvd : (U₀.subgroupOf B).index ∣ U₀.index := by
    have := Subgroup.relIndex_dvd_index_of_le hUB
    rwa [Subgroup.relIndex] at this
  have hodd : ¬ 2 ∣ (U₀.subgroupOf B).index := fun h => hUi (h.trans hdvd)
  have hpel : ∀ b ∈ B, (∃ k : ℕ, b ^ (2 ^ k) = 1) → b ∈ U₀ := by
    intro b hb ⟨k, hk⟩
    set q : B ⧸ U₀.subgroupOf B := QuotientGroup.mk ⟨b, hb⟩ with hq
    have h1 : q ^ (2 ^ k) = 1 := by
      rw [hq, ← QuotientGroup.mk_pow]
      have : (⟨b, hb⟩ : B) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
      rw [this]; rfl
    have h2 : q ^ (U₀.subgroupOf B).index = 1 := by
      rw [Subgroup.index_eq_card]; exact pow_card_eq_one'
    have hcop : Nat.Coprime (2 ^ k) (U₀.subgroupOf B).index :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    have h3 : orderOf q ∣ Nat.gcd (2 ^ k) (U₀.subgroupOf B).index :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [hcop] at h3
    have h4 : q = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
    have h5 : (⟨b, hb⟩ : B) ∈ U₀.subgroupOf B := (QuotientGroup.eq_one_iff _).1 h4
    exact h5
  have hUU₀ : (U : Subgroup Z) = U₀ := by
    have hUle : (U : Subgroup Z) ≤ U₀ := by
      intro x hx
      have hxB : x ∈ B := by
        rw [← hUnorm]; exact Subgroup.le_normalizer hx
      refine hpel x hxB ?_
      obtain ⟨k, hk⟩ := U.isPGroup' ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hc1 := Sylow.card_eq_multiplicity U
    have hc2 := Sylow.card_eq_multiplicity Us
    have hcard : Nat.card U₀ ≤ Nat.card (U : Subgroup Z) := by
      have : Nat.card (Us : Subgroup Z) = Nat.card (U : Subgroup Z) := by rw [hc1, hc2]
      exact le_of_eq this
    exact Subgroup.eq_of_le_of_card_ge hUle hcard
  refine ⟨U, hUnorm, ?_, ?_⟩
  · rw [hUU₀]
    refine ⟨hUB, ?_, hnormB, hpel, ?_, hUp⟩
    · intro b hb
      have hb' : b ∈ U₀ ⊔ (B ⊓ N) := by rw [hUH]; exact hb
      obtain ⟨u, hu, h, hh, rfl⟩ := uc22p20j_mem_sup_of_le_normalizer
        (inf_le_left.trans hBnorm) hb'
      refine ⟨h, hh, h⁻¹ * u * h, ?_, by group⟩
      simpa using hnormB h⁻¹ (B.inv_mem (Subgroup.mem_inf.1 hh).1) u hu
    · intro g hg
      have := uc22p20j_mem_normalizer_of_conj_le hg
      rwa [← hUU₀, hUnorm] at this
  · haveI : (U₀.subgroupOf B).Normal := hUn
    haveI : Group.IsSolvable (U₀.subgroupOf B) := by
      have hP : IsPGroup 2 (U₀.subgroupOf B) := hUp.comap_subtype (K := B)
      haveI : Group.IsNilpotent (U₀.subgroupOf B) := hP.isNilpotent
      infer_instance
    haveI : Group.IsSolvable (B ⧸ U₀.subgroupOf B) := by
      refine CFSG.FeitThompson.isSolvable_of_odd_natCard _ ?_
      rw [← Subgroup.index_eq_card]
      exact (Nat.odd_iff.2 (by omega : (U₀.subgroupOf B).index % 2 = 1))
    exact Group.isSolvable_of_subgroup_quotient (U₀.subgroupOf B)

open CFSG.RankThree.PartTwo.Sec18 in
theorem uc22p20j_sandwich_of_isSplitBNPair {B N : Subgroup Z}
    (hBN : CFSG.ASVolI.ChIJK.IsSplitBNPair 2 B N) (U₁ : Sylow 2 Z) (Y : Subgroup Z)
    (hY : (U₁ : Subgroup Z) ≤ Y) :
    ∃ P : Subgroup Z, normalizer ((U₁ : Subgroup Z) : Set Z) ≤ P ∧ Y ≤ P ∧
      Hinf P ≤ Y := by
  haveI : (cartan B N).Normal := hBN.normal_inter
  obtain ⟨U, hUnorm, hSU, hsolv⟩ := uc22p20j_exists_splitUnit hBN
  obtain ⟨S, hbn⟩ := CFSG.ASVolI.ChIJK.burnsideI2BN_exists_isBNPair
    (CFSG.ASVolI.ChIJK.burnsideI2BN_toPre hBN)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Z U U₁
  have hmem : ∀ x : Z, x ∈ (U₁ : Subgroup Z) ↔ g⁻¹ * x * g ∈ (U : Subgroup Z) := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.conj_apply, mul_assoc]
  let Y' : Subgroup Z := Y.comap (MulAut.conj g).toMonoidHom
  have hUY' : (U : Subgroup Z) ≤ Y' := by
    intro u hu
    show g * u * g⁻¹ ∈ Y
    apply hY
    rw [hmem]
    have e : g⁻¹ * (g * u * g⁻¹) * g = u := by group
    rw [e]; exact hu
  obtain ⟨P', hBP', hYP', hP'⟩ := uc22p20j_sandwich_abstract hbn hSU hsolv hUY'
  let P : Subgroup Z := P'.comap (MulAut.conj g⁻¹).toMonoidHom
  have hPmem : ∀ x : Z, x ∈ P ↔ g⁻¹ * x * g ∈ P' := by
    intro x; show (MulAut.conj g⁻¹) x ∈ P' ↔ _; simp [MulAut.conj_apply]
  refine ⟨P, ?_, ?_, ?_⟩
  · intro x hx
    rw [hPmem]
    apply hBP'
    rw [← hUnorm, Subgroup.mem_normalizer_iff]
    intro h
    have h1 := Subgroup.mem_normalizer_iff.1 hx (g * h * g⁻¹)
    rw [hmem, hmem] at h1
    have e : g⁻¹ * (x * (g * h * g⁻¹) * x⁻¹) * g = (g⁻¹ * x * g) * h * (g⁻¹ * x * g)⁻¹ := by group
    simpa [e, mul_assoc] using h1
  · intro y hy
    rw [hPmem]
    apply hYP'
    show g * (g⁻¹ * y * g) * g⁻¹ ∈ Y
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [e]; exact hy
  · set Q := CFSG.inSubgroup CFSG.perfectResidual P with hQ
    have hQP : Q ≤ P := Subgroup.map_subtype_le _
    have hQperf : ⁅Q, Q⁆ = Q := commutator_inSubgroup_perfectResidual P
    set Q' := Q.map (MulAut.conj g⁻¹).toMonoidHom with hQ'
    have hQ'perf : ⁅Q', Q'⁆ = Q' := by
      rw [hQ', ← Subgroup.map_commutator, hQperf]
    have hconj : ∀ x : Z, (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
      intro x; simp [MulAut.conj_apply]
    have hQ'P' : Q' ≤ P' := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hconj]
      exact (hPmem x).1 (hQP hx)
    have h1 : Q' ≤ Y' := (le_inSubgroup_perfectResidual hQ'perf hQ'P').trans hP'
    intro x hx
    have h2 : (MulAut.conj g⁻¹).toMonoidHom x ∈ Y' := h1 ⟨x, hx, rfl⟩
    rw [hconj] at h2
    have h3 : g * (g⁻¹ * x * g) * g⁻¹ ∈ Y := h2
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at h3

@[expose] def uc22p20jSandwich (X : Type) [Group X] [Finite X] : Prop :=
  ∀ U : Sylow 2 X, ∀ Y : Subgroup X, (U : Subgroup X) ≤ Y →
    ∃ P : Subgroup X, normalizer (U : Set X) ≤ P ∧ Y ≤ P ∧ Hinf P ≤ Y

theorem uc22p20j_sandwich_of_splitBN {Z : Type} [Group Z] [Finite Z] {B N : Subgroup Z}
    (hBN : IsSplitBNPair 2 B N) : uc22p20jSandwich Z := by
  exact fun U Y hY => uc22p20j_sandwich_of_isSplitBNPair hBN U Y hY

end Transport

end CFSG.LocalAnalysis.UniquenessCase.UC22
