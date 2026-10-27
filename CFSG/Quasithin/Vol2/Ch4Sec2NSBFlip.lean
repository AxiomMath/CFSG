module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBDefs
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213C2
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBTwist
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

private theorem mem_normalizer_centralizer_flip {G : Type} [Group G] {V : Subgroup G} {g : G}
    (hV : g ∈ Subgroup.normalizer (V : Set G)) :
    ∀ c ∈ Subgroup.centralizer (V : Set G), g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := (Subgroup.mem_normalizer_iff''.mp hV v).mp hv
  have h1 := (Subgroup.mem_centralizer_iff.mp hc) _ hv'
  calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * v := by group

private theorem mem_normalizer_commutator_flip {G : Type} [Group G] {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((⁅X, Y⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hX hY ⊢
  rw [Subgroup.map_commutator, hX, hY]

private theorem transvection_mulVec_nsb2i {m : ℕ} (i j : Fin m) (w : Fin m → ZMod 2) :
    (Matrix.transvection i j (1 : ZMod 2)).mulVec w = w + Pi.single i (w j) := by
  funext l
  simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, Pi.single_apply,
    Function.update_apply]

private noncomputable def transvGL_nsb2i {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    Matrix.GeneralLinearGroup (Fin m) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mk'' (Matrix.transvection i j (1 : ZMod 2))
    (by rw [Matrix.det_transvection_of_ne i j hij 1]; exact isUnit_one)

private theorem transvGL_sq_nsb2i {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    transvGL_nsb2i hij * transvGL_nsb2i hij = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  show Matrix.transvection i j (1 : ZMod 2) * Matrix.transvection i j (1 : ZMod 2) = 1
  rw [Matrix.transvection_mul_transvection_same i j hij, show (1 : ZMod 2) + 1 = 0 by decide,
    Matrix.transvection_zero]

private theorem mem_sup_of_le_normalizer_nsb2i {G : Type} [Group G] {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, (a₂⁻¹ * b₁ * a₂) * b₂, B.mul_mem ?_ hb₂, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hA (A.inv_mem ha₂)) b₁).1 hb₁
        simpa using this
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, ?_, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hA ha) b⁻¹).1 (B.inv_mem hb)
        exact this }
  have hAS : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩
  have hBS : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩
  exact (_root_.sup_le hAS hBS) hx

theorem exists_involution_act {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G}
    {m k : ℕ} (hd : NoSumBigData G T M L Mm I H K m k) :
    ∃ l₀ ∈ L, l₀ ∉ Subgroup.centralizer (vV T L : Set G) ∧
      l₀ ^ 2 ∈ Subgroup.centralizer (vV T L : Set G) := by
  obtain ⟨-, -, c, hm34, hmk, -, -, hsum⟩ := hd
  obtain ⟨α, hα, hkerα, -, -, β, hβs, -, hβe⟩ := hsum
  have hm2 : 2 ≤ m := by rcases hm34 with h | h <;> omega
  have hk : 0 < k := by omega
  obtain ⟨e0, e1, hne⟩ : ∃ e0 e1 : Fin m, e0 ≠ e1 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, fun h => by simpa using congrArg Fin.val h⟩
  have hτmem : transvGL_nsb2i hne ∈ CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2) := by
    rw [statedSL_zmod_two_eq_top]
    exact Subgroup.mem_top _
  obtain ⟨τS, hτS⟩ : ∃ τS : ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)),
      (τS : Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) = transvGL_nsb2i hne :=
    ⟨⟨transvGL_nsb2i hne, hτmem⟩, rfl⟩
  have hτS_sq : τS * τS = 1 := by
    apply Subtype.ext
    show (τS : Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) *
      (τS : Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) = 1
    rw [hτS]
    exact transvGL_sq_nsb2i hne
  obtain ⟨a, ha⟩ := hα τS
  have hRN : pCoreOf 2 I ≤ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G) :=
    c.hypC28.le_M.trans c.LH_normal
  have hax : (a : G) ∈ pCoreOf 2 I ⊔ perfectCore (L ⊓ H) := by
    rw [sup_comm]
    exact a.2
  obtain ⟨r, hr, l, hl, hal⟩ := mem_sup_of_le_normalizer_nsb2i hRN hax
  have hlA : l ∈ perfectCore (L ⊓ H) ⊔ pCoreOf 2 I := Subgroup.mem_sup_left hl
  have hrA : r ∈ perfectCore (L ⊓ H) ⊔ pCoreOf 2 I := Subgroup.mem_sup_right hr
  have hlL : l ∈ L := (le_trans (perfectCore_le (L ⊓ H)) inf_le_left) hl
  have hαr : α ⟨r, hrA⟩ = 1 := by
    have hmem : (⟨r, hrA⟩ : ↥(perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) ∈ α.ker := by
      rw [hkerα]
      exact Subgroup.mem_subgroupOf.mpr hr
    exact MonoidHom.mem_ker.mp hmem
  have hαl : α ⟨l, hlA⟩ = τS := by
    have hdec : (⟨l, hlA⟩ : ↥(perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) =
        (⟨r, hrA⟩ : ↥(perfectCore (L ⊓ H) ⊔ pCoreOf 2 I))⁻¹ * a :=
      Subtype.ext (by
        show l = r⁻¹ * (a : G)
        rw [hal]
        group)
    rw [hdec, map_mul, map_inv, hαr, inv_one, one_mul, ha]
  have hnotC : l ∉ Subgroup.centralizer (vV T L : Set G) := by
    intro hC
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd
      (Pi.single (⟨0, hk⟩ : Fin k) (Pi.single e1 (1 : ZMod 2) : Fin m → ZMod 2)))
    have hui : Multiplicative.toAdd (β u) ⟨0, hk⟩ = Pi.single e1 (1 : ZMod 2) := by
      simp [hu]
    have hfix : (u : G) = l * (u : G) * l⁻¹ := by
      have h1 : (u : G) * l = l * (u : G) := Subgroup.mem_centralizer_iff.mp hC (u : G) u.2
      rw [← h1]
      simp
    have hβu := hβe ⟨l, hlA⟩ u u hfix ⟨0, hk⟩
    have hG : (α ⟨l, hlA⟩ : Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) =
        transvGL_nsb2i hne := by
      rw [hαl, hτS]
    have hmod : moduleAct false
        ((α ⟨l, hlA⟩ : ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2))) :
          Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) =
        Matrix.transvection e0 e1 (1 : ZMod 2) := by
      rw [hG]
      rfl
    rw [hui, hmod, transvection_mulVec_nsb2i] at hβu
    have h2 := congrFun hβu e0
    simp [Pi.single_apply] at h2
  have hsq : l ^ 2 ∈ pCoreOf 2 I := by
    have hmem : (⟨l, hlA⟩ : ↥(perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) ^ 2 ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_pow, hαl, pow_two, hτS_sq]
    rw [hkerα, Subgroup.mem_subgroupOf] at hmem
    simpa using hmem
  exact ⟨l, hlL, hnotC, c.pCoreOf_le_centralizer_V c.R_le hsq⟩

theorem localFlip_of (h323 : Lemma323') (hF : FlipCore) : LocalFlip := by
  intro G _ _ T M L Mm I H K m k hch hIV g hg h1 h2 h3
  have hd : NoSumBigData G T M L Mm I H K m k := hch.1
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  obtain ⟨hV, hcomm⟩ := hF G T M L Mm I H K m k hch hIV g hg h1 h2 h3
  obtain ⟨l₀, hl₀L, hl₀V, hl₀2⟩ := exists_involution_act hd
  have hLV : L ≤ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) := by
    have hRN : L ⊔ T ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) := by
      rw [← hc.omega_eq]
      exact (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_omegaOneCenterOf _)
    intro l hl
    exact mem_normalizer_commutator_flip (hRN (Subgroup.mem_sup_left hl)) (Subgroup.le_normalizer hl)
  have hgN : g ∈ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) :=
    A4.mem_normalizer_of_conj_mem hV
  set y := g * l₀ * g⁻¹ with hy
  have hyN : y ∈ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN (hLV hl₀L)) (Subgroup.inv_mem _ hgN)
  have hzL : ∀ l ∈ L, ⁅y, l⁆ ∈ Subgroup.centralizer (vV T L : Set G) :=
    fun l hl => hcomm l hl l₀ hl₀L
  obtain ⟨e, he, hye⟩ := h323 G T M L Mm I H K m k hd y hyN hzL
  have hy2 : y ^ 2 ∈ Subgroup.centralizer (vV T L : Set G) := by
    have : y ^ 2 = g * l₀ ^ 2 * g⁻¹ := by
      rw [hy, pow_two, pow_two]
      group
    rw [this]
    exact mem_normalizer_centralizer_flip hgN _ hl₀2
  obtain ⟨f, rfl⟩ := he
  have hyC : y ∈ Subgroup.centralizer (vV T L : Set G) := by
    have e1 : y = y ^ (2 * f + 1) * (y ^ 2)⁻¹ ^ f := by group
    rw [e1]
    exact Subgroup.mul_mem _ hye (Subgroup.pow_mem _ (Subgroup.inv_mem _ hy2) f)
  apply hl₀V
  have : l₀ = g⁻¹ * y * g⁻¹⁻¹ := by
    rw [hy]
    group
  rw [this]
  exact mem_normalizer_centralizer_flip (Subgroup.inv_mem _ hgN) _ hyC

end CFSG.Quasithin.H13.Ch4.NSB
