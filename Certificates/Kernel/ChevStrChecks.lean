module

public import Certificates.Data.Kernel.ChevStrK
public import CFSG.Blueprint.ChevalleyStringsInputs

public section

open CFSG.Blueprint.Chevalley CFSG.KC.ChevStr

namespace CertificateChecks.ChevStr

theorem ch114_g2_top : top Tag.G2.rank 19 (2 * g2StringData.maxCoord + 1) g2Certificate.roots
    g2StringData.strings = true := by decide +kernel
theorem ch114_f4_top : top Tag.F4.rank 93 (2 * f4StringData.maxCoord + 1) f4Certificate.roots
    f4StringData.strings = true := by decide +kernel
theorem ch114_d4_top : top Tag.D4.rank 41 (2 * d4StringData.maxCoord + 1) d4Certificate.roots
    d4StringData.strings = true := by decide +kernel
theorem ch114_e6_top : top Tag.E6.rank 198 (2 * e6StringData.maxCoord + 1) e6Certificate.roots
    e6StringData.strings = true := by decide +kernel
theorem ch114_e7_top : top Tag.E7.rank 355 (2 * e7StringData.maxCoord + 1) e7Certificate.roots
    e7StringData.strings = true := by decide +kernel
theorem ch114_e8_top : top Tag.E8.rank 961 (2 * e8StringData.maxCoord + 1) e8Certificate.roots
    e8StringData.strings = true := by decide +kernel

theorem ch114_g2_coords : coordsK Tag.G2.rank g2StringData.maxCoord g2Certificate.roots = true := by
  decide +kernel
theorem ch114_f4_coords : coordsK Tag.F4.rank f4StringData.maxCoord f4Certificate.roots = true := by
  decide +kernel
theorem ch114_d4_coords : coordsK Tag.D4.rank d4StringData.maxCoord d4Certificate.roots = true := by
  decide +kernel
theorem ch114_e6_coords : coordsK Tag.E6.rank e6StringData.maxCoord e6Certificate.roots = true := by
  decide +kernel
theorem ch114_e7_coords : coordsK Tag.E7.rank e7StringData.maxCoord e7Certificate.roots = true := by
  decide +kernel
theorem ch114_e8_coords : coordsK Tag.E8.rank e8StringData.maxCoord e8Certificate.roots = true := by
  decide +kernel

theorem ch114_g2_buckets : g2StringData.checkBuckets g2Certificate = true := by decide +kernel
theorem ch114_f4_buckets : f4StringData.checkBuckets f4Certificate = true := by decide +kernel
theorem ch114_d4_buckets : d4StringData.checkBuckets d4Certificate = true := by decide +kernel
theorem ch114_e6_buckets : e6StringData.checkBuckets e6Certificate = true := by decide +kernel
theorem ch114_e7_buckets : e7StringData.checkBuckets e7Certificate = true := by decide +kernel
theorem ch114_e8_buckets : e8StringData.checkBuckets e8Certificate = true := by decide +kernel

theorem ch114_g2_bounds : g2StringData.checkBucketBounds g2Certificate = true := by decide +kernel
theorem ch114_f4_bounds : f4StringData.checkBucketBounds f4Certificate = true := by decide +kernel
theorem ch114_d4_bounds : d4StringData.checkBucketBounds d4Certificate = true := by decide +kernel
theorem ch114_e6_bounds : e6StringData.checkBucketBounds e6Certificate = true := by decide +kernel
theorem ch114_e7_bounds : e7StringData.checkBucketBounds e7Certificate = true := by decide +kernel
theorem ch114_e8_bounds : e8StringData.checkBucketBounds e8Certificate = true := by decide +kernel

theorem ch114_neg_string : top Tag.G2.rank 19 7 g2Certificate.roots
    [192, 4, 48, 56, 145, 1, 193, 1, 96, 100, 4, 144] = false := by decide +kernel

theorem ch114_neg_root : top Tag.G2.rank 19 7 [137, 152, 135, 185, 153, 120, 87, 187, 169, 119, 86, 103]
    g2StringData.strings = false := by decide +kernel

theorem ch114_neg_modulus : top Tag.G2.rank 2 7 g2Certificate.roots g2StringData.strings = false := by
  decide +kernel

theorem ch114_neg_coords : coordsK Tag.E8.rank 5 e8Certificate.roots = false := by decide +kernel

end CertificateChecks.ChevStr

end
