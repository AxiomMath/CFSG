module

public import CFSG.Quasithin.MS93.S38EFFHyp
public import CFSG.Quasithin.MS93.S38OffHat
public import CFSG.Quasithin.MS93.S38OffVI

public section

namespace CFSG.Quasithin.MS93.S38EA

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S38E
open scoped commutatorElement

variable {G : Type} [Group G] {M T L : Subgroup G}
variable {S' : Type} [CommGroup S']

structure IsO2Rep (L : Subgroup G) (ρ : ↥M →* MulAut S') : Prop where
  pCore : ∀ m : ↥M, (m : G) ∈ pCoreOf 2 M → ρ m = 1
  ne : ∃ l : ↥M, (l : G) ∈ L ∧ ρ l ≠ 1

namespace IsO2Rep

variable {ρ : ↥M →* MulAut S'}

theorem not_le_kerG (hρ : IsO2Rep L ρ) : ¬ L ≤ IsIrrRep.kerG ρ := by
  intro hL
  obtain ⟨l, hl, hne⟩ := hρ.ne
  obtain ⟨k, hk, hkl⟩ := hL hl
  apply hne
  have : k = l := Subtype.ext hkl
  rw [← this]
  exact hk

theorem cent [Finite G] (hρ : IsO2Rep L ρ) (h : PUHyp M T L) :
    ∀ c ∈ ρ.range, (∀ k ∈ IsIrrRep.imL L ρ, c * k = k * c) → ∀ e : ℕ, c ^ 2 ^ e = 1 →
      c = 1 := by
  rintro _ ⟨m, rfl⟩ hck e he
  obtain ⟨k, hk, f, hf⟩ := exists_pow_isTwoElt ρ m he
  rw [← hk]
  set m' := m ^ k
  have hm'Q : (m' : G) ∈ pCoreOf 2 M := by
    refine h.mem_pCoreOf_of_rel IsIrrRep.le_normalizer_kerG hρ.not_le_kerG m'.2
      ⟨f, by simpa using congrArg Subtype.val hf⟩ fun l hl => ?_
    refine ⟨⁅m', ⟨l, h.L_le hl⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm, hk]
    exact hck _ ⟨⟨l, h.L_le hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  exact hρ.pCore _ hm'Q

theorem map_le_imL [Finite G] (hρ : IsO2Rep L ρ) (h : PUHyp M T L) {F : Subgroup G}
    (hF2 : ∀ m ∈ F, m * m = 1)
    (hl : ∀ m ∈ F, ∃ l : ↥L, (∃ a : ℕ, l ^ 2 ^ a = 1) ∧ ∃ N : Subgroup G, N ≤ M ∧
      M ≤ Subgroup.normalizer (N : Set G) ∧ ¬ L ≤ N ∧ (l : G)⁻¹ * m ∈ N) :
    (F.subgroupOf M).map ρ ≤ IsIrrRep.imL L ρ := by
  rintro _ ⟨m, hm, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hm
  obtain ⟨l, ⟨a, hla⟩, N, hNM, hNn, hLN, hlm⟩ := hl m hm
  have hcomm := h.commutator_le_pCoreOf_M hNM hNn hLN
  set lM : ↥M := ⟨l, h.L_le l.2⟩
  set c : ↥M := lM⁻¹ * m with hc
  have hcN : (c : G) ∈ N := hlm
  have hcK : ∀ k ∈ IsIrrRep.imL L ρ, ρ c * k = k * ρ c := by
    rintro _ ⟨l', hl', rfl⟩
    have hmem : ((⁅c, l'⁆ : ↥M) : G) ∈ pCoreOf 2 M :=
      hcomm (Subgroup.commutator_mem_commutator hcN (Subgroup.mem_subgroupOf.mp hl'))
    have h1 := hρ.pCore _ hmem
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hcl : Commute (ρ c) (ρ lM) := hcK _ ⟨lM, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
  have hρm : ρ m = ρ lM * ρ c := by rw [hc, map_mul, map_inv, mul_inv_cancel_left]
  have hρc : ρ c = (ρ lM)⁻¹ * ρ m := by rw [hρm, inv_mul_cancel_left]
  have hml : Commute (ρ lM)⁻¹ (ρ m) := by
    rw [hρm]
    exact ((Commute.refl _).mul_right hcl.symm).inv_left
  have hm2 : ρ m ^ 2 = 1 := by
    have : m ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact hF2 _ hm)
    rw [← map_pow, this, map_one]
  have hl2 : ρ lM ^ 2 ^ a = 1 := by
    have : lM ^ 2 ^ a = 1 := Subtype.ext (by simpa using congrArg Subtype.val hla)
    rw [← map_pow, this, map_one]
  have hpow : ρ c ^ 2 ^ (a + 1) = 1 := by
    have e1 : ρ m ^ 2 ^ (a + 1) = 1 := by rw [pow_succ', pow_mul, hm2, one_pow]
    have e2 : ρ lM ^ 2 ^ (a + 1) = 1 := by rw [pow_succ, pow_mul, hl2, one_pow]
    rw [hρc, hml.mul_pow, inv_pow, e1, e2, inv_one, one_mul]
  have hc1 := hρ.cent h (ρ c) ⟨c, rfl⟩ hcK (a + 1) hpow
  exact ⟨lM, Subgroup.mem_subgroupOf.mpr l.2, by rw [hρm, hc1, mul_one]⟩

end IsO2Rep

section Cases

variable [Finite G]

omit [Finite G] in
theorem le_normalizer_map_ker {H : Type} [Group H] (r : ↥M →* H) :
    M ≤ Subgroup.normalizer ((r.ker.map M.subtype : Subgroup G) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ m : ↥M, ∀ x ∈ r.ker.map M.subtype,
      (m : G) * x * (m : G)⁻¹ ∈ r.ker.map M.subtype := by
    rintro m _ ⟨k, hk, rfl⟩
    refine ⟨m * k * m⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hk ⊢
    rw [map_mul, map_mul, hk, mul_one, map_inv, mul_inv_cancel]
  intro x
  refine ⟨key ⟨m, hm⟩ x, fun hx => ?_⟩
  have := key ⟨m, hm⟩⁻¹ _ hx
  simpa [mul_assoc] using this

theorem exists_l_of_isHatA6U (h : PUHyp M T L) (hX : IsHatA6U M T L) {F : Subgroup G}
    (hF : IsXOff M T F) {m : G} (hm : m ∈ F) :
    ∃ l : ↥L, (∃ a : ℕ, l ^ 2 ^ a = 1) ∧ ∃ N : Subgroup G, N ≤ M ∧
      M ≤ Subgroup.normalizer (N : Set G) ∧ ¬ L ≤ N ∧ (l : G)⁻¹ * m ∈ N := by
  obtain ⟨-, -, hU, h6⟩ := hX
  have hFT : F ≤ T := hF.1
  have hFN : F ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    hFT.trans (S38H.le_normalizer_Uq_T h)
  have hLN : L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.L_le.trans (le_normalizer_Uq h.le_normalizer)
  obtain ⟨hFL, -⟩ := S38H.offender_facts hU h h6 hF
  have hmL := hFL (convI_mem_autI hU hm (hFN hm))
  obtain ⟨g, hgL, hgm⟩ := (mem_autI hU).1 hmL
  have hm2 : convI hU g ^ 2 ^ 1 = 1 := by
    rw [hgm, pow_one, pow_two, ← map_mul]
    have : (⟨m, hFN hm⟩ * ⟨m, hFN hm⟩ : Subgroup.normalizer (Uq M T L : Set G)) = 1 :=
      Subtype.ext (by simpa [pow_two] using hF.2.1.2 m hm)
    rw [this, map_one]
  obtain ⟨k, hk, f, hf⟩ := exists_pow_isTwoElt (convI hU) g hm2
  refine ⟨⟨(g ^ k : Subgroup.normalizer (Uq M T L : Set G)), ?_⟩, ⟨f, ?_⟩,
    M ⊓ Subgroup.centralizer (Uq M T L : Set G), inf_le_left,
    le_normalizer_inf Subgroup.le_normalizer
      (le_normalizer_centralizer (le_normalizer_Uq h.le_normalizer)),
    fun hle => h.not_le_centralizer_of_Uq_le le_rfl (hle.trans inf_le_right), ?_⟩
  · simpa using L.pow_mem hgL k
  · apply Subtype.ext
    simpa using congrArg Subtype.val hf
  · refine ⟨M.mul_mem (M.inv_mem (h.L_le (by simpa using L.pow_mem hgL k))) (hF.1.trans h.le hm),
      ?_⟩
    have h1 : convI hU ((g ^ k)⁻¹ * ⟨m, hFN hm⟩) = 1 := by
      rw [map_mul, map_inv, hk, hgm, inv_mul_cancel]
    have h2 := (convI_eq_one_iff hU _).mp h1
    simpa using h2

theorem psi_eq_alpha (h : PUHyp M T L) (D : OffVI.A6Data M T L) (l : ↥L) :
    OffVI.psi D h ⟨l, h.L_le l.2⟩ = (D.α₀ l : Equiv.Perm (Fin 6)) := by
  refine OffVI.eq_of_crd (D := D) fun u hu => ?_
  have h1 := OffVI.psi_spec (D := D) h (h.L_le l.2) hu
  rw [OffVI.homOf_of_mem (h.L_le l.2)] at h1
  rw [← h1]
  exact OffVI.crd_conj (h.L_le.trans (le_normalizer_Uq h.le_normalizer)) D.equiv l hu

theorem exists_l_of_a6Data (h : PUHyp M T L) (D : OffVI.A6Data M T L) {F : Subgroup G}
    (hF : IsXOff M T F) {m : G} (hm : m ∈ F) :
    ∃ l : ↥L, (∃ a : ℕ, l ^ 2 ^ a = 1) ∧ ∃ N : Subgroup G, N ≤ M ∧
      M ≤ Subgroup.normalizer (N : Set G) ∧ ¬ L ≤ N ∧ (l : G)⁻¹ * m ∈ N := by
  have hmM : m ∈ M := hF.1.trans h.le hm
  set r := OffVI.psi D h with hr
  let φ : ↥L →* Equiv.Perm (Fin 6) := r.comp (Subgroup.inclusion h.L_le)
  set l₀ := OffVI.lOf D ⟨m, hmM⟩ with hl₀
  have hφl₀ : φ l₀ = r ⟨m, hmM⟩ := by
    show r ⟨l₀, h.L_le l₀.2⟩ = r ⟨m, hmM⟩
    rw [psi_eq_alpha h D l₀]
    rfl
  have hm2 : φ l₀ ^ 2 ^ 1 = 1 := by
    rw [hφl₀, pow_one, pow_two, ← map_mul]
    have : (⟨m, hmM⟩ * ⟨m, hmM⟩ : ↥M) = 1 :=
      Subtype.ext (by simpa [pow_two] using hF.2.1.2 m hm)
    rw [this, map_one]
  obtain ⟨k, hk, f, hf⟩ := exists_pow_isTwoElt φ l₀ hm2
  refine ⟨l₀ ^ k, ⟨f, hf⟩, r.ker.map M.subtype, Subgroup.map_subtype_le _,
    le_normalizer_map_ker r, fun hle => ?_, ?_⟩
  ·
    have hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
    have hcomm : ⁅Uq M T L, L⁆ ≤ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.commutator_le]
      intro u hu l hl
      obtain ⟨n, hn, hnl⟩ := hle hl
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hn
      have hlM : l ∈ M := h.L_le hl
      have hn' : n = ⟨l, hlM⟩ := Subtype.ext hnl
      have hlu : l * u⁻¹ * l⁻¹ ∈ Uq M T L :=
        (Subgroup.mem_normalizer_iff.mp (hMU hlM) _).mp ((Uq M T L).inv_mem hu)
      have hcu : ⁅u, l⁆ ∈ Uq M T L ⊓ Zq M L := by
        have e : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [e, ← OffVI.crd_eq_zero_iff D.ker ((Uq M T L).mul_mem hu hlu),
          OffVI.crd_mul hu hlu, OffVI.psi_spec h hlM ((Uq M T L).inv_mem hu),
          OffVI.homOf_of_mem hlM, ← hn', hn, A6F.actChi_one, OffVI.crd_inv hu]
        exact add_neg_cancel _
      rw [h.Uq_inf_Zq] at hcu
      exact hcu.2
    apply h.not_le_centralizer_of_Uq_le le_rfl
    rw [← Subgroup.le_centralizer_iff, ← h.Uq_comm]
    exact hcomm
  · refine ⟨⟨_, M.mul_mem (M.inv_mem (h.L_le (l₀ ^ k).2)) hmM⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have e : (⟨((l₀ ^ k : ↥L) : G)⁻¹ * m, M.mul_mem (M.inv_mem (h.L_le (l₀ ^ k).2)) hmM⟩ : ↥M) =
        (⟨(l₀ ^ k : ↥L), h.L_le (l₀ ^ k).2⟩ : ↥M)⁻¹ * ⟨m, hmM⟩ := rfl
    rw [e, map_mul, map_inv]
    have : r ⟨(l₀ ^ k : ↥L), h.L_le (l₀ ^ k).2⟩ = φ (l₀ ^ k) := rfl
    rw [this, hk, hφl₀, inv_mul_cancel]

end Cases

section Ext

variable [Finite G] {W S : Type} [CommGroup W] [CommGroup S]

theorem eq_one_of_ext (h : PUHyp M T L) (hW : ∀ w : W, w ^ 2 = 1) {ρW : ↥M →* MulAut W}
    {ρS : ↥M →* MulAut S} (hρW : IsO2Rep L ρW) (hρS : ∃ l : ↥M, (l : G) ∈ L ∧ ρS l ≠ 1)
    (q : W →* S) (hq : ∀ m w, q (ρW m w) = ρS m (q w))
    (hZ : ∀ m : ↥M, (m : G) ∈ L → ∀ z, q z = 1 → ρW m z = z)
    (m : ↥M) (hmL : (m : G) ∈ L) (hm : ρS m = 1) : ρW m = 1 := by
  let N : Subgroup G := L ⊓ ρS.ker.map M.subtype
  have hNM : N ≤ M := inf_le_left.trans h.L_le
  have hNn : M ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_inf h.le_normalizer (le_normalizer_map_ker ρS)
  have hLN : ¬ L ≤ N := by
    intro hle
    obtain ⟨x, hxL, hx1⟩ := hρS
    obtain ⟨z, hz, hzx⟩ := (hle hxL).2
    apply hx1
    rw [← show z = x from Subtype.ext hzx]
    exact hz
  have hcomm := h.commutator_le_pCoreOf_M hNM hNn hLN
  have hmN : (m : G) ∈ N := ⟨hmL, ⟨m, hm, rfl⟩⟩
  have hcK : ∀ k ∈ IsIrrRep.imL L ρW, ρW m * k = k * ρW m := by
    rintro _ ⟨l', hl', rfl⟩
    have hmem : ((⁅m, l'⁆ : ↥M) : G) ∈ pCoreOf 2 M :=
      hcomm (Subgroup.commutator_mem_commutator hmN (Subgroup.mem_subgroupOf.mp hl'))
    have h1 := hρW.pCore _ hmem
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hxx : ρW m * ρW m = 1 := by
    ext w
    rw [MulAut.mul_apply, MulAut.one_apply]
    set d := ρW m w * w⁻¹ with hd
    have hqd : q d = 1 := by rw [hd, map_mul, map_inv, hq, hm, MulAut.one_apply, mul_inv_cancel]
    have hxd : ρW m d = d := hZ m hmL d hqd
    have hxw : ρW m w = d * w := by rw [hd, inv_mul_cancel_right]
    rw [hxw, map_mul, hxd, hxw, ← mul_assoc, ← pow_two, hW, one_mul]
  have hsq : ρW m ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hxx
  exact hρW.cent h _ ⟨m, rfl⟩ hcK 1 hsq

end Ext

end CFSG.Quasithin.MS93.S38EA
