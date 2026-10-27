module

public import CFSG.Quasithin.EmptyFaithful.ModFA5Blk
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hall
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCZ
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.ModF

open scoped Pointwise
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 CFSG.LieType.BorelTits
  Equiv

variable {G : Type} [Group G]

structure A5Cfg (I S Iz K₁ K₂ : Subgroup G) : Prop where
  min : MinParabolic I S Iz
  blk₁ : IsBlock2 I K₁
  blk₂ : IsBlock2 I K₂
  a5₁ : IsAltType K₁ 5
  a5₂ : IsAltType K₂ 5
  comm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  perm₁ : ∀ t ∈ S, B6.conjSub t K₁ = K₁ ∨ B6.conjSub t K₁ = K₂
  perm₂ : ∀ t ∈ S, B6.conjSub t K₂ = K₁ ∨ B6.conjSub t K₂ = K₂
  gen : I = S ⊔ (K₁ ⊔ K₂)

variable {I S Iz K₁ K₂ : Subgroup G}

theorem A5Cfg.symm (c : A5Cfg I S Iz K₁ K₂) : A5Cfg I S Iz K₂ K₁ :=
  ⟨c.min, c.blk₂, c.blk₁, c.a5₂, c.a5₁, fun a ha b hb => (c.comm b hb a ha).symm,
    fun t ht => (c.perm₂ t ht).symm, fun t ht => (c.perm₁ t ht).symm,
    by rw [c.gen, sup_comm K₂ K₁]⟩

theorem isSylowTwoOf_of_le {X : Subgroup G} (hS : IsSylowTwoOf S I) (hSX : S ≤ X) (hXI : X ≤ I) :
    IsSylowTwoOf S X := by
  refine ⟨hSX, hS.isPGroup, fun hdvd => hS.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex S X I hSX hXI
  have h2 : 2 ∣ S.relIndex I := by rw [← h1]; exact Dvd.dvd.mul_right hdvd _
  exact h2

theorem mem_pCoreOf_of_conj_mem (hS : IsPGroup 2 S) {g : G} (hg : g ∈ I)
    (h : ∀ x ∈ I, x * g * x⁻¹ ∈ S) : g ∈ pCoreOf 2 I := by
  let N : Subgroup G :=
    { carrier := {g | g ∈ I ∧ ∀ x ∈ I, x * g * x⁻¹ ∈ S}
      one_mem' := ⟨I.one_mem, fun x _ => by simp⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨I.mul_mem ha.1 hb.1, fun x hx => by
          have := S.mul_mem (ha.2 x hx) (hb.2 x hx)
          simpa [mul_assoc] using this⟩
      inv_mem' := fun {a} ha =>
        ⟨I.inv_mem ha.1, fun x hx => by
          have := S.inv_mem (ha.2 x hx)
          simpa [mul_assoc] using this⟩ }
  have hmemN : ∀ g, g ∈ N ↔ g ∈ I ∧ ∀ x ∈ I, x * g * x⁻¹ ∈ S := fun g => Iff.rfl
  have hNS : N ≤ S := fun g hg => by simpa using ((hmemN g).mp hg).2 1 I.one_mem
  have hN2 : IsPGroup 2 N := hS.to_le hNS
  have hnorm : I ≤ Subgroup.normalizer (N : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨hgI, hg⟩
      refine ⟨I.mul_mem (I.mul_mem hy hgI) (I.inv_mem hy), fun x hx => ?_⟩
      have := hg (x * y) (I.mul_mem hx hy)
      simpa [mul_assoc] using this
    · rintro ⟨hgI, hg⟩
      refine ⟨?_, fun x hx => ?_⟩
      · have := I.mul_mem (I.mul_mem (I.inv_mem hy) hgI) hy
        simpa [mul_assoc] using this
      · have := hg (x * y⁻¹) (I.mul_mem hx (I.inv_mem hy))
        simpa [mul_assoc] using this
  exact le_pCoreOf_of_le_normalizer 2 (fun g hg => ((hmemN g).mp hg).1) hnorm hN2 ⟨hg, h⟩

theorem mem_normalizer_of_conjSub_eq {a : G} {X : Subgroup G} (h : B6.conjSub a X = X) :
    a ∈ Subgroup.normalizer (X : Set G) := by
  refine B6.mem_normalizer_of_conjSub_le h.le ?_
  have : B6.conjSub a⁻¹ X = X := by
    conv_lhs => rw [← h]
    rw [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  exact this.le

variable [Finite G]

namespace A5Cfg

variable (c : A5Cfg I S Iz K₁ K₂)
include c

omit [Finite G] in
theorem sylow : IsSylowTwoOf S I := c.min.isSylow

omit [Finite G] in
theorem S_le_Iz : S ≤ Iz := c.min.le

omit [Finite G] in
theorem Iz_le_I : Iz ≤ I := c.min.maximal.1.le

omit [Finite G] in
theorem sylowIz : IsSylowTwoOf S Iz := isSylowTwoOf_of_le c.sylow c.S_le_Iz c.Iz_le_I

omit [Finite G] in
theorem le₁ : K₁ ≤ I := c.blk₁.2.1

omit [Finite G] in
theorem le₂ : K₂ ≤ I := c.blk₂.2.1

omit [Finite G] in
theorem K₁_le_normalizer₂ : K₁ ≤ Subgroup.normalizer (K₂ : Set G) :=
  Lin2.le_normalizer_of_commute (A := K₂) (B := K₁) fun a ha b hb => (c.comm b hb a ha).symm

theorem sylow₁ : IsSylowTwoOf (S ⊓ K₁) K₁ :=
  RankOneRecog.isSylowTwoOf_inf_of_subnormal c.sylow c.le₁ c.blk₁.2.2

theorem pCore_le₁ : pCoreOf 2 K₁ ≤ S ⊓ K₁ := c.sylow₁.pCoreOf_le

omit [Finite G] in
theorem inf_mem_pCore₁ {x : G} (hx₁ : x ∈ K₁) (hx₂ : x ∈ K₂) : x ∈ pCoreOf 2 K₁ := by
  obtain ⟨α, hα, hαk, -⟩ := c.a5₁
  have hcenter : α ⟨x, hx₁⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := hα z
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (c.comm y y.2 x hx₂)
  rw [alternatingGroup.center_eq_bot (α := Fin 5) (by simp)] at hcenter
  have h1 : α ⟨x, hx₁⟩ = 1 := Subgroup.mem_bot.mp hcenter
  have h2 : (⟨x, hx₁⟩ : ↥K₁) ∈ CFSG.pCore 2 ↥K₁ := by rw [← hαk]; exact h1
  exact (AppC.mem_pCore_iff_mem_blockQ _).mp h2

theorem ker_le₁ {α : ↥K₁ →* alternatingGroup (Fin 5)} (hαk : α.ker = CFSG.pCore 2 K₁) :
    ∀ x : ↥K₁, α x = 1 → (x : G) ∈ S := by
  intro x hx
  have h1 : x ∈ CFSG.pCore 2 ↥K₁ := by rw [← hαk]; exact hx
  have h2 := (AppC.mem_pCore_iff_mem_blockQ x).mp h1
  exact (c.pCore_le₁ h2).1

theorem normalizer_le_Iz₁ {α : ↥K₁ →* alternatingGroup (Fin 5)} (hα : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 K₁) :
    ∀ b ∈ K₁, b ∈ Subgroup.normalizer ((S ⊓ K₁ : Subgroup G) : Set G) → b ∈ Iz := by
  have hP₁ := c.sylow₁
  have hP₂ := c.symm.sylow₁
  have hker := c.ker_le₁ hαk
  have hnotN := not_le_normalizer hα hker hP₁
  have hinf : K₁ ⊓ K₂ ≤ (S ⊓ K₁) ⊓ (S ⊓ K₂) := by
    intro x hx
    exact ⟨c.pCore_le₁ (c.inf_mem_pCore₁ hx.1 hx.2),
      c.symm.pCore_le₁ (c.symm.inf_mem_pCore₁ hx.2 hx.1)⟩
  have hB : IsSylowTwoOf ((S ⊓ K₁) ⊔ (S ⊓ K₂)) (K₁ ⊔ K₂) :=
    isSylowTwoOf_sup_of_commuting c.comm hP₁ hP₂ hinf
  set B := (S ⊓ K₁) ⊔ (S ⊓ K₂) with hBdef
  have hSB : ∀ s ∈ S, B6.conjSub s B ≤ B := by
    intro s hs
    have hS' : B6.conjSub s S = S := B6.conjSub_eq_self (Subgroup.le_normalizer hs)
    rw [hBdef, OrderIso.map_sup, OrderIso.map_inf, OrderIso.map_inf, hS']
    refine sup_le ?_ ?_
    · rcases c.perm₁ s hs with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    · rcases c.perm₂ s hs with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
  have hSY : S ≤ I ⊓ Subgroup.normalizer (B : Set G) := fun s hs =>
    ⟨c.sylow.le hs, B6.mem_normalizer_of_conjSub_le (hSB s hs) (hSB s⁻¹ (S.inv_mem hs))⟩
  have hN₁ : K₁ ≤ Subgroup.normalizer ((S ⊓ K₂ : Subgroup G) : Set G) :=
    Lin2.le_normalizer_of_commute (A := S ⊓ K₂) (B := K₁) fun p hp a ha => (c.comm a ha p hp.2).symm
  have hBK₁ : B ⊓ K₁ ≤ S ⊓ K₁ := by
    rintro x ⟨hxB, hx₁⟩
    have hx' : x ∈ ((S ⊓ K₁ : Subgroup G) : Set G) * ((S ⊓ K₂ : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (S ⊓ K₁) (S ⊓ K₂) (inf_le_right.trans hN₁)]
      exact hxB
    obtain ⟨u, hu, v, hv, rfl⟩ := hx'
    have hv₁ : v ∈ K₁ := by
      have := K₁.mul_mem (K₁.inv_mem hu.2) hx₁
      simpa using this
    have hv' : v ∈ S ⊓ K₁ := (hinf ⟨hv₁, hv.2⟩).1
    exact (S ⊓ K₁).mul_mem hu hv'
  have hYI : I ⊓ Subgroup.normalizer (B : Set G) < I := by
    refine lt_of_le_of_ne inf_le_left fun hYI => hnotN ?_
    intro l hl
    have hlB : l ∈ Subgroup.normalizer (B : Set G) := by
      have : l ∈ I ⊓ Subgroup.normalizer (B : Set G) := by rw [hYI]; exact c.le₁ hl
      exact this.2
    have h1 := Subgroup.inf_normalizer_le_normalizer_inf ⟨hlB, Subgroup.le_normalizer hl⟩
    have heq : B ⊓ K₁ = S ⊓ K₁ := le_antisymm hBK₁ (le_inf le_sup_left inf_le_right)
    rwa [heq] at h1
  have hle : I ⊓ Subgroup.normalizer (B : Set G) ≤ Iz := c.min.le_of_lt hSY hYI
  intro b hb hbN
  have hbN' : b ∈ Subgroup.normalizer ((S ⊓ K₂ : Subgroup G) : Set G) := hN₁ hb
  have hbB : b ∈ Subgroup.normalizer (B : Set G) := by
    refine B6.mem_normalizer_of_conjSub_le ?_ ?_
    · rw [hBdef, OrderIso.map_sup, B6.conjSub_eq_self hbN, B6.conjSub_eq_self hbN']
    · have hbN1 := Subgroup.inv_mem _ hbN
      have hbN2 := Subgroup.inv_mem _ hbN'
      rw [hBdef, OrderIso.map_sup, B6.conjSub_eq_self hbN1, B6.conjSub_eq_self hbN2]
  exact hle ⟨c.le₁ hb, hbB⟩

theorem exists_nonTwo₁ : ∃ c₀ : G, c₀ ∈ K₁ ∧ c₀ ∈ Iz ∧ ∀ n : ℕ, c₀ ^ (2 ^ n) ≠ 1 := by
  obtain ⟨α, hα, hαk, -⟩ := c.a5₁
  have hker := c.ker_le₁ hαk
  obtain ⟨c₀, hc₀N, hγ3, hγ1, -, -⟩ :=
    exists_normalizing_lift hα hker c.sylow₁ (i := 0) (j := 1) (by decide)
  refine ⟨c₀, c₀.2, c.normalizer_le_Iz₁ hα hαk _ c₀.2 hc₀N, fun n hn => ?_⟩
  have h0 : c₀ ^ (2 ^ n) = 1 := Subtype.ext (by simpa using hn)
  have h1 : (toPerm α c₀) ^ (2 ^ n) = 1 := by rw [← map_pow, h0, map_one]
  have hg : (toPerm α c₀) ^ (Nat.gcd (2 ^ n) 3) = 1 := pow_gcd_eq_one.mpr ⟨h1, hγ3⟩
  have hcop : Nat.gcd (2 ^ n) 3 = 1 := Nat.Coprime.pow_left n (by norm_num)
  rw [hcop, pow_one] at hg
  exact hγ1 hg

omit [Finite G] in
theorem R_le_S : pCoreOf 2 Iz ≤ S := c.sylowIz.pCoreOf_le

theorem not_swap₁ {a : G} (ha : a ∈ pCoreOf 2 Iz) : ¬ B6.conjSub a K₁ = K₂ := by
  intro hconj
  obtain ⟨c₀, hc₁, hcIz, hnot⟩ := c.exists_nonTwo₁
  have hR2 : IsPGroup 2 (pCoreOf 2 Iz) := pCoreOf_isPGroup 2 Iz
  have hnorm := le_normalizer_pCoreOf 2 Iz
  have h1 : c₀ * a⁻¹ * c₀⁻¹ ∈ pCoreOf 2 Iz :=
    (Subgroup.mem_normalizer_iff.mp (hnorm hcIz) a⁻¹).mp ((pCoreOf 2 Iz).inv_mem ha)
  have hxR : a * c₀ * a⁻¹ * c₀⁻¹ ∈ pCoreOf 2 Iz := by
    have := (pCoreOf 2 Iz).mul_mem ha h1
    simpa [mul_assoc] using this
  have hk₂K : a * c₀ * a⁻¹ ∈ K₂ := by
    rw [← hconj, B6.mem_conjSub]
    simpa [mul_assoc] using hc₁
  have hcomm : c₀⁻¹ * (a * c₀ * a⁻¹) = (a * c₀ * a⁻¹) * c₀⁻¹ := c.comm _ (K₁.inv_mem hc₁) _ hk₂K
  obtain ⟨n, hn⟩ := hR2 ⟨_, hxR⟩
  have hxn : (a * c₀ * a⁻¹ * c₀⁻¹) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hxfact : (a * c₀ * a⁻¹ * c₀⁻¹) ^ (2 ^ n) =
      (a * c₀ * a⁻¹) ^ (2 ^ n) * (c₀⁻¹) ^ (2 ^ n) :=
    Commute.mul_pow (show Commute (a * c₀ * a⁻¹) c₀⁻¹ from hcomm.symm) _
  rw [hxn] at hxfact
  have hkc : (a * c₀ * a⁻¹) ^ (2 ^ n) = c₀ ^ (2 ^ n) := by
    have h := hxfact.symm
    rw [inv_pow] at h
    exact mul_inv_eq_one.mp h
  have hmem₁ : c₀ ^ (2 ^ n) ∈ K₁ := K₁.pow_mem hc₁ _
  have hmem₂ : c₀ ^ (2 ^ n) ∈ K₂ := by rw [← hkc]; exact K₂.pow_mem hk₂K _
  have hO := c.inf_mem_pCore₁ hmem₁ hmem₂
  obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 K₁ ⟨_, hO⟩
  apply hnot (n + m)
  have h2 : (c₀ ^ (2 ^ n)) ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  rw [← pow_mul, ← pow_add] at h2
  exact h2

theorem R_le_normalizer₁ : pCoreOf 2 Iz ≤ Subgroup.normalizer (K₁ : Set G) := by
  intro a ha
  rcases c.perm₁ a (c.R_le_S ha) with h | h
  · exact mem_normalizer_of_conjSub_eq h
  · exact absurd h (c.not_swap₁ ha)

theorem R_le_normalizer₂ : pCoreOf 2 Iz ≤ Subgroup.normalizer (K₂ : Set G) :=
  c.symm.R_le_normalizer₁

end A5Cfg

end CFSG.Quasithin.ModF
