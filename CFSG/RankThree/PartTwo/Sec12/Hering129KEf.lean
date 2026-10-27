module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KEa
public import CFSG.RankThree.PartTwo.Sec12.Hering129KEh
public import CFSG.RankThree.PartTwo.Sec12.Hering129KEc
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
public import CFSG.RankThree.PartTwo.Sec12.Hering129HEnd
public import CFSG.RankThree.PartTwo.Sec13.Item136E
public import CFSG.RankThree.PartTwo.Sec13.Item137Tools
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Transport

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129KEf

section Lift

variable {H : Type} [Group H] [Finite H]

theorem exists_lift {Y A : Subgroup H} (hT : aschbacherSolvableCore 3 H ≤ Y)
    (hA3 : IsPGroup 3 A) {Fh : Subgroup (H ⧸ aschbacherSolvableCore 3 H)}
    (hFY : Fh ≤ Y.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) (hFp : IsPGroup 3 Fh)
    (hBN : A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) ≤
      Subgroup.normalizer (Fh : Set (H ⧸ aschbacherSolvableCore 3 H))) :
    ∃ F : Subgroup H, F ≤ Y ∧ IsPGroup 3 F ∧
      F.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) = Fh ∧
      A ≤ Subgroup.normalizer (F : Set H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hπ
  set Bh := A.map π with hBh
  have hBp : IsPGroup 3 Bh := hA3.map π
  have hB : IsPGroup 3 ↥(Fh ⊔ Bh) := Hering129KEa.isPGroup_sup_of_le_normalizer hFp hBp hBN
  obtain ⟨S, hAS, -, hS3, hSB⟩ := Sec13.exists_isPGroup_le_map_eq (M := ⊤) (B := Fh ⊔ Bh) hB
    (by rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)]; exact le_top)
    hA3 le_top (le_sup_right : Bh ≤ Fh ⊔ Bh)
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hS3
  refine ⟨S ⊓ Fh.comap π, ?_, hS3.to_le inf_le_left, ?_, ?_⟩
  · intro f hf
    obtain ⟨y, hy, hyf⟩ := hFY (Subgroup.mem_comap.mp hf.2)
    have : y⁻¹ * f ∈ aschbacherSolvableCore 3 H := by
      rw [← QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 H)]
      change π (y⁻¹ * f) = 1
      rw [map_mul, map_inv, hyf, inv_mul_cancel]
    have hf' : f = y * (y⁻¹ * f) := by group
    rw [hf']
    exact Y.mul_mem hy (hT this)
  · ext f
    constructor
    · rintro ⟨s, ⟨-, hsF⟩, rfl⟩
      exact hsF
    · intro hf
      have hf' : f ∈ S.map π := hSB ▸ Subgroup.mem_sup_left hf
      obtain ⟨s, hs, rfl⟩ := hf'
      exact ⟨s, ⟨hs, hf⟩, rfl⟩
  · intro a ha
    refine Subgroup.mem_normalizer_fintype fun f hf => ⟨?_, ?_⟩
    · exact S.mul_mem (S.mul_mem (hAS ha) hf.1) (S.inv_mem (hAS ha))
    · have hπa : π a ∈ Subgroup.normalizer (Fh : Set (H ⧸ aschbacherSolvableCore 3 H)) :=
        hBN (Subgroup.mem_map_of_mem π ha)
      have := (Subgroup.mem_normalizer_iff.mp hπa (π f)).mp hf.2
      simpa using this

end Lift

section Central

variable {H : Type} [Group H] [Finite H]

theorem normal_zpowers_of_central {x : H} (hxc : ∀ h : H, x * h = h * x) :
    (Subgroup.zpowers x).Normal :=
  ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : g * x ^ k * g⁻¹ = x ^ k := by
      rw [(Commute.zpow_right (show Commute g x from (hxc g).symm) k).eq, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.zpow_mem_zpowers x k⟩

theorem zpow_eq_one_or_mem {x : H} (hx3 : x ^ 3 = 1) {S : Subgroup H} {k : ℤ}
    (h : x ^ k ∈ S) : x ^ k = 1 ∨ x ∈ S := by
  have hk : x ^ k = x ^ (k % 3) := by
    have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
    conv_lhs => rw [← Int.mul_ediv_add_emod k 3]
    rw [_root_.zpow_add, _root_.zpow_mul, h3, _root_.one_zpow, one_mul]
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h0 | h1 | h2
  · left
    rw [hk, h0, zpow_zero]
  · right
    rw [hk, h1, zpow_one] at h
    exact h
  · right
    rw [hk, h2] at h
    have h22 : x = x ^ (2 : ℤ) * x ^ (2 : ℤ) := by
      rw [← zpow_add]
      have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
      calc x = x ^ (3 : ℤ) * x := by rw [h3, one_mul]
        _ = x ^ (2 + 2 : ℤ) := by rw [← zpow_add_one]; norm_num
    rw [h22]
    exact S.mul_mem h h

theorem mem_normalizer_sup_of_central {x n : H} (hxc : ∀ h : H, x * h = h * x)
    {F : Subgroup H} (hn : n ∈ Subgroup.normalizer (F : Set H)) :
    n ∈ Subgroup.normalizer ((Subgroup.zpowers x ⊔ F : Subgroup H) : Set H) := by
  haveI := normal_zpowers_of_central hxc
  refine Subgroup.mem_normalizer_fintype fun e he => ?_
  obtain ⟨m, hm, f, hf, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp he
  have hnf : n * f * n⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hn f).mp hf
  have hnm : n * m * n⁻¹ = m := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    rw [(Commute.zpow_right (show Commute n x from (hxc n).symm) k).eq, mul_inv_cancel_right]
  have : n * (m * f) * n⁻¹ = m * (n * f * n⁻¹) := by
    calc n * (m * f) * n⁻¹ = (n * m * n⁻¹) * (n * f * n⁻¹) := by group
      _ = m * (n * f * n⁻¹) := by rw [hnm]
  rw [this]
  exact Subgroup.mul_mem_sup hm hnf

theorem mem_normalizer_inf_of_normal {n : H} {E Y : Subgroup H} [Y.Normal]
    (hn : n ∈ Subgroup.normalizer (E : Set H)) :
    n ∈ Subgroup.normalizer ((E ⊓ Y : Subgroup H) : Set H) := by
  refine Subgroup.mem_normalizer_fintype fun f hf => ?_
  exact ⟨(Subgroup.mem_normalizer_iff.mp hn f).mp hf.1, Subgroup.Normal.conj_mem ‹_› f hf.2 n⟩

end Central

end Hering129KEf

section Main


open CFSG.Assembly.RankThreeEven (projSL)

theorem exists_E_of_hess (hL3 : Gap129HessL3) (hD4 : Gap129HessD4)
    {H : Type} [Group H] [Finite H] {Y A : Subgroup H} {x b c : H}
    (hYn : Y.Normal) (hY : Y ∈ thetaComponents 3 H) (hYA : Y ⊔ A = ⊤)
    (hAel : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hgen : A = Subgroup.zpowers x ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers c)
    (hx1 : x ≠ 1) (hxc : ∀ h : H, x * h = h * x) (hxY : x ∉ Y) (hcY : c ∈ Y)
    (hbxc : b ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers c)
    (hAC : A ⊓ Sec4.thetaQuotCentralizer Y = Subgroup.zpowers x)
    (hX : ∃ X : Subgroup H, X ≤ Y ∧ X ≤ Subgroup.centralizer ({b} : Set H) ∧
      Group.IsPerfect X ∧ (X.subgroupOf (Y ⊓ Subgroup.centralizer ({b} : Set H))).IsSubnormal ∧
      c ∈ X ∧ ∃ (p n : ℕ) (_ : Fact p.Prime), 4 ≤ p ^ n ∧
        Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSL 2 (GaloisField p n)))
    (hkind : ∀ e ∈ A, ¬ KFacts.InducesStdKind Y e .field ∧
      ¬ KFacts.InducesStdKind Y e .graphField)
    (hty : (∃ (p e : ℕ) (_ : Fact p.Prime),
        Sec4.IsoLThreePi (Y ⧸ aschbacherSolvableCore 3 Y) p e) ∨
      ∃ (r : TauCeti.PrimePower) (hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid), r.p = 2 ∧
        Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃*
          (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group)) :
    ∃ E : Subgroup H, Typ129IIIcE A c Y x E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAel.2 a a.2)⟩
  have hxA : x ∈ A := hgen ▸ Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hbA : b ∈ A := hgen ▸ Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hcA : c ∈ A := hgen ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hx3 : x ^ 3 = 1 := hAel.2 x hxA
  have hb3 : b ^ 3 = 1 := hAel.2 b hbA
  have hc3 : c ^ 3 = 1 := hAel.2 c hcA
  have hT : aschbacherSolvableCore 3 H ≤ Y := by
    haveI := hYn
    exact Hering129KEa.theta_le_of_sup_eq_top hA3 hYA
  have hHD := hessData_of_core hYn hY hT hAel hA27 hgen hb3 hxc hcY hAC hX hkind
  obtain ⟨η, -⟩ := (theta_component_quotient_structure (G := H) Nat.prime_three hY).2.2.1
  have hconcl : HessConcl (Y.map π) (A.map π) (π b) (π c) := by
    rcases hty with ⟨p, e, hp, hiso⟩ | ⟨r, hr, hr2, ⟨ee⟩⟩
    · refine hL3 _ _ _ _ _ _ hHD ⟨p, e, hp, ?_⟩
      rcases hiso with ⟨h1, ⟨f⟩⟩ | ⟨h2, ⟨f⟩⟩
      · exact Or.inl ⟨h1, ⟨η.symm.trans f⟩⟩
      · exact Or.inr ⟨h2, ⟨η.symm.trans f⟩⟩
    · exact hD4 _ _ _ _ _ _ hHD ⟨r, hr, hr2, ⟨η.symm.trans ee⟩⟩
  obtain ⟨Fh, hFY, hFel, hF9, hcF, hBN, hFB, hcomm, hne, htrans, ⟨hsl⟩⟩ := hconcl
  have hFp : IsPGroup 3 Fh := fun f => ⟨1, Subtype.ext (by simpa using hFel.2 f f.2)⟩
  obtain ⟨F, hFYle, hFp3, hFmap, hAF⟩ := Hering129KEf.exists_lift hT hA3 hFY hFp hBN
  have hFA3 : IsPGroup 3 ↥(F ⊔ A) :=
    Hering129KEa.isPGroup_sup_of_le_normalizer hFp3 hA3 hAF
  have hinjFA : Set.InjOn π ((F ⊔ A : Subgroup H) : Set H) :=
    injOn_mk_of_isPGroup Nat.prime_three hFA3
  have hFAF : F ≤ F ⊔ A := le_sup_left
  have hAFA : A ≤ F ⊔ A := le_sup_right
  have hinjF : Set.InjOn π (F : Set H) := hinjFA.mono hFAF
  have hFel' : CFSG.Assembly.IsElemAbelian 3 F :=
    Sec13.isElemAbelian_of_injOn π hinjF (hFmap ▸ hFel)
  have hF9' : Nat.card F = 9 := by
    rw [← Sec13.card_map_eq_of_injOn π hinjF, hFmap, hF9]
  have hcF' : c ∈ F := by
    have h1 : π c ∈ F.map π := hFmap ▸ hcF
    obtain ⟨f, hf, hfc⟩ := h1
    exact (hinjFA (hFAF hf) (hAFA hcA) hfc) ▸ hf
  have hxF : x ∉ F := fun h => hxY (hFYle h)
  haveI hxN : (Subgroup.zpowers x).Normal := Hering129KEf.normal_zpowers_of_central hxc
  obtain ⟨hEab, hE27⟩ := Sec13.isElemAbelian_zpowers_sup_of_card_nine hx3 hxF le_rfl hF9'
    hFel'.2 (fun y _ => hxc y)
  set E : Subgroup H := Subgroup.zpowers x ⊔ F with hEdef
  have hEY : E ⊓ Y = F := by
    refine le_antisymm ?_ (le_inf le_sup_right hFYle)
    rintro e ⟨he, heY⟩
    obtain ⟨m, hm, f, hf, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp he
    have hmY : m ∈ Y := by
      have := Y.mul_mem heY (Y.inv_mem (hFYle hf))
      simpa using this
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    rcases Hering129KEf.zpow_eq_one_or_mem hx3 hmY with h1 | h1
    · rw [h1, one_mul]
      exact hf
    · exact absurd h1 hxY
  have hπc3 : (π c) ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  obtain ⟨f₀, hf₀F, hf₀c⟩ : ∃ f₀ ∈ Fh, f₀ ∉ Subgroup.zpowers (π c) := by
    by_contra hcon
    push_neg at hcon
    have hle : Fh ≤ Subgroup.zpowers (π c) := hcon
    have h1 := Subgroup.card_le_of_le hle
    rw [hF9, Nat.card_zpowers] at h1
    have h2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hπc3)
    omega
  have hf₀1 : f₀ ≠ 1 := fun h => hf₀c (h ▸ Subgroup.one_mem _)
  obtain ⟨nh, ⟨hnhY, hnhN⟩, hnhc⟩ := htrans f₀ hf₀F hf₀1
  have hnh : nh ∈ (Subgroup.normalizer (F : Set H)).map π := by
    rw [← Sec13.normalizer_map_mk_eq hFp3, hFmap]
    exact hnhN
  obtain ⟨n, hnN, rfl⟩ := hnh
  have hnY : n ∈ Y := by
    obtain ⟨y, hy, hyn⟩ := hnhY
    have h1 : y⁻¹ * n ∈ aschbacherSolvableCore 3 H := by
      refine (QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 H) _).mp ?_
      change π (y⁻¹ * n) = 1
      rw [map_mul, map_inv, hyn, inv_mul_cancel]
    have hn' : n = y * (y⁻¹ * n) := by group
    rw [hn']
    exact Y.mul_mem hy (hT h1)
  have hnE : n ∈ Subgroup.normalizer (E : Set H) :=
    Hering129KEf.mem_normalizer_sup_of_central hxc hnN
  have hnotc : n ∉ Subgroup.normalizer (Subgroup.zpowers c : Set H) := by
    intro hnc
    have h1 : n * c * n⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp hnc c).mp (Subgroup.mem_zpowers c)
    have h2 : π (n * c * n⁻¹) ∈ Subgroup.zpowers (π c) := by
      rw [← MonoidHom.map_zpowers]
      exact Subgroup.mem_map_of_mem π h1
    rw [map_mul, map_mul, map_inv] at h2
    exact hf₀c (hnhc ▸ h2)
  have hnm : ∀ m ∈ Subgroup.zpowers x, n * m * n⁻¹ = m := fun m hm => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    rw [(Commute.zpow_right (show Commute n x from (hxc n).symm) k).eq, mul_inv_cancel_right]
  have hnF : ∀ n', n' ∈ Subgroup.normalizer (E : Set H) → n' ∈ Subgroup.normalizer (F : Set H) := by
    intro n' hn'
    haveI := hYn
    have := Hering129KEf.mem_normalizer_inf_of_normal (Y := Y) hn'
    rwa [hEY] at this
  refine ⟨E, ⟨hEab, hE27⟩, ?_, ⟨Subgroup.mem_sup_right hcF', hcY⟩,
    fun h => hnotc (h ⟨hnY, hnE⟩), ?_, ?_⟩
  · rw [hEY]
  ·
    have hbNF : b ∈ Subgroup.normalizer (F : Set H) := hAF hbA
    have hcommF : ∀ f ∈ F, b * f * b⁻¹ * f⁻¹ ∈ Subgroup.zpowers c := by
      intro f hf
      have hg : b * f * b⁻¹ * f⁻¹ ∈ F ⊔ A :=
        (F ⊔ A).mul_mem ((F ⊔ A).mul_mem ((F ⊔ A).mul_mem (hAFA hbA) (hFAF hf))
          ((F ⊔ A).inv_mem (hAFA hbA))) ((F ⊔ A).inv_mem (hFAF hf))
      have h1 := hcomm (π f) (hFmap ▸ Subgroup.mem_map_of_mem π hf)
      rw [← MonoidHom.map_zpowers] at h1
      obtain ⟨g', hg', hg'e⟩ := h1
      have hg'A : g' ∈ F ⊔ A := hAFA (Subgroup.zpowers_le.mpr hcA hg')
      have := hinjFA hg'A hg (by rw [hg'e]; simp only [map_mul, map_inv])
      exact this ▸ hg'
    have hneF : ∃ f ∈ F, b * f * b⁻¹ * f⁻¹ ≠ 1 := by
      obtain ⟨fh, hfh, hfh1⟩ := hne
      have h1 : fh ∈ F.map π := hFmap ▸ hfh
      obtain ⟨f, hf, rfl⟩ := h1
      refine ⟨f, hf, fun h1 => hfh1 ?_⟩
      have h2 : π (b * f * b⁻¹ * f⁻¹) = 1 := by rw [h1, map_one]
      simpa only [map_mul, map_inv] using h2
    obtain ⟨hbF, hU27, hUheis, hUc⟩ := Hering129KEh.isHeisThree_sup_zpowers hFel' hF9' hb3
      hbNF hcF' hcommF hneF
    refine ⟨Subgroup.zpowers x, F ⊔ Subgroup.zpowers b, ?_, ?_, ?_, ?_, hUheis⟩
    · apply le_antisymm
      · refine sup_le (sup_le le_sup_left (le_sup_of_le_right le_sup_left)) ?_
        rw [hgen]
        exact sup_le (sup_le le_sup_left (le_sup_of_le_right le_sup_right))
          (le_sup_of_le_right (le_sup_of_le_left (Subgroup.zpowers_le.mpr hcF')))
      · refine sup_le (le_sup_of_le_left le_sup_left) (sup_le ?_ ?_)
        · exact le_sup_of_le_left le_sup_right
        · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hbA)
    · rw [eq_bot_iff]
      rintro z ⟨hz, hzU⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rcases Hering129KEf.zpow_eq_one_or_mem hx3 hzU with h1 | h1
      · rw [h1]
        exact Subgroup.one_mem _
      · exfalso
        have hAU : A ≤ F ⊔ Subgroup.zpowers b := by
          rw [hgen]
          exact sup_le (sup_le (Subgroup.zpowers_le.mpr h1) le_sup_right)
            (le_sup_of_le_left (Subgroup.zpowers_le.mpr hcF'))
        have hUA : A = F ⊔ Subgroup.zpowers b :=
          Subgroup.eq_of_le_of_card_ge hAU (by rw [hU27, hA27])
        obtain ⟨f, hf, hfne⟩ := hneF
        apply hfne
        have hfU : f ∈ A := hUA ▸ (Subgroup.mem_sup_left hf : f ∈ F ⊔ Subgroup.zpowers b)
        have hbU : b ∈ A := hbA
        have hcm := hAel.1.is_comm.comm ⟨b, hbU⟩ ⟨f, hfU⟩
        have hcm' : b * f = f * b := congrArg Subtype.val hcm
        calc b * f * b⁻¹ * f⁻¹ = (b * f) * b⁻¹ * f⁻¹ := by group
          _ = (f * b) * b⁻¹ * f⁻¹ := by rw [hcm']
          _ = 1 := by group
    · rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
    · intro z hz u _
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.zpow_left (hxc u) k).eq
  ·
    rw [hYA]
    have hYhBh : Y.map π ⊔ A.map π = ⊤ := by
      rw [← Subgroup.map_sup, hYA, Subgroup.map_top_of_surjective π hπs]
    rw [hYhBh] at hsl
    rw [Sec4.Sporadic.autIn_top_eq_range] at hsl ⊢
    let α : ↥(Subgroup.normalizer (E : Set H)) →* ↥(Subgroup.normalizer (Fh : Set _)) :=
      (π.comp (Subgroup.normalizer (E : Set H)).subtype).codRestrict _ (fun n' => by
        have := Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π (hnF n' n'.2))
        rwa [hFmap] at this)
    have hα : Function.Surjective α := by
      rintro ⟨nh', hnh'⟩
      have h1 : nh' ∈ (Subgroup.normalizer (F : Set H)).map π := by
        rw [← Sec13.normalizer_map_mk_eq hFp3, hFmap]
        exact hnh'
      obtain ⟨n', hn'F, rfl⟩ := h1
      exact ⟨⟨n', Hering129KEf.mem_normalizer_sup_of_central hxc hn'F⟩, rfl⟩
    have hker : ((Fh.normalizerMonoidHom).comp α).ker = (E.normalizerMonoidHom).ker := by
      ext ⟨n', hn'⟩
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
      constructor
      · intro h
        refine MulEquiv.ext fun ⟨e, he⟩ => Subtype.ext ?_
        change n' * e * n'⁻¹ = e
        obtain ⟨m, hm, f, hf, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp he
        have hnm' : n' * m * n'⁻¹ = m := by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
          rw [(Commute.zpow_right (show Commute n' x from (hxc n').symm) k).eq,
            mul_inv_cancel_right]
        have hnf : n' * f * n'⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp (hnF n' hn') f).mp hf
        have hfh : π f ∈ Fh := hFmap ▸ Subgroup.mem_map_of_mem π hf
        have hπ1 : π (n' * f * n'⁻¹) = π f := by
          have h1 := congrArg (fun φ : MulAut Fh => (φ ⟨π f, hfh⟩ : Fh).1) h
          have h1' : π n' * π f * (π n')⁻¹ = π f := h1
          rw [map_mul, map_mul, map_inv]
          exact h1'
        have h2 : n' * f * n'⁻¹ = f := hinjF hnf hf hπ1
        calc n' * (m * f) * n'⁻¹ = (n' * m * n'⁻¹) * (n' * f * n'⁻¹) := by group
          _ = m * f := by rw [hnm', h2]
      · intro h
        refine MulEquiv.ext fun ⟨fh, hfh⟩ => Subtype.ext ?_
        change π n' * fh * (π n')⁻¹ = fh
        have h1 : fh ∈ F.map π := hFmap ▸ hfh
        obtain ⟨f, hf, rfl⟩ := h1
        have hEf : f ∈ E := Subgroup.mem_sup_right hf
        have h2 := congrArg (fun φ : MulAut E => (φ ⟨f, hEf⟩ : E).1) h
        have h3 : n' * f * n'⁻¹ = f := by
          simpa [Sec4.normalizerMonoidHom_apply_coe] using h2
        rw [← map_inv, ← map_mul, ← map_mul, h3]
    obtain ⟨eR⟩ := Hering129KEa.nonempty_range_mulEquiv E.normalizerMonoidHom
      Fh.normalizerMonoidHom α hα hker
    exact ⟨eR.trans hsl⟩

end Main

end CFSG.RankThree.PartTwo.Sec12
